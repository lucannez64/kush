//! Tasks, threads and channels on the machine (FND-EVAL-EFFECTS): one valid
//! schedule, cooperative, with a FIFO ready queue.
//!
//! - Each task has its own frame stack, handler stack and continuation
//!   stack; a switch swaps them into the machine. A task's body frame is
//!   entered when it first runs, and returns to [`Site::TaskEnd`].
//! - An operation that blocks (a join, a yield, a full channel) returns
//!   [`Flow::Suspend`] with the rest of its work; the run loop resumes it
//!   when the scheduler picks the task again.
//! - A task counts two allocations (its control block and stack) from its
//!   spawn to its join, and the root two for the whole run (kush.c counts a
//!   result buffer too). A thread is a task that inherits no handlers and is never
//!   cancelled; its join yields its payload.
//! - A panic in a task ends it; its join raises the panic in the joiner.
//!   `Task.scope` joins its children even when its body panics, after
//!   cancelling them when the panic unwinds (always, in a task or a
//!   `Task.catch`), and `Task.catch` turns a panic into `Err(Panic {})`.

use super::*;
use crate::executable::{SliceOp, TaskExitShape};
use std::collections::VecDeque;

/// How a task ended.
#[derive(Clone)]
pub(super) enum Outcome {
    /// Its result, and whether it carries an obligation (`preserve`).
    Completed(Words, bool),
    Cancelled,
    Failed(Diagnostic),
}

#[derive(Clone, Copy, PartialEq)]
pub(super) enum State {
    Ready,
    Running,
    Blocked,
    Finished,
}

/// The rest of an operation once a task's outcome is known (a join).
type OnOutcome = Box<dyn for<'p, 'o, 'm> FnOnce(&'m mut Machine<'p, 'o>, Outcome) -> Run<Flow>>;

/// The rest of a scope once its children are joined: the first child's
/// panic, if any.
type OnEnd =
    Box<dyn for<'p, 'o, 'm> FnOnce(&'m mut Machine<'p, 'o>, Option<Diagnostic>) -> Run<Flow>>;

/// A suspended operation: the rest of its work, then where its result goes.
pub(super) struct Resume {
    pub(super) then: Then,
    pub(super) site: Site,
    pub(super) unwind: Option<BlockId>,
}

pub(super) struct TaskRecord {
    pub(super) state: State,
    /// The task's stacks while another task runs.
    pub(super) stack: Vec<Frame>,
    pub(super) handlers: Vec<effects::HandlerFrame>,
    pub(super) kstack: effects::KStack,
    pub(super) unwinding: Option<Diagnostic>,
    /// The body to enter when the task first runs: its function and
    /// environment.
    pub(super) start: Option<(Code, i64)>,
    pub(super) resume: Option<Resume>,
    pub(super) cancelled: bool,
    pub(super) waiter: Option<usize>,
    pub(super) outcome: Option<Outcome>,
    /// A join has started (the bookkeeping is freed once it is finished).
    pub(super) claimed: bool,
    /// The spawning task, for structured cancellation (none for a thread).
    pub(super) parent: Option<usize>,
    /// The children of each open `Task.scope`, in spawn order.
    pub(super) scopes: Vec<Vec<usize>>,
    pub(super) joined: std::collections::BTreeSet<usize>,
    pub(super) root: bool,
    pub(super) catch_depth: usize,
    pub(super) preserve: bool,
    /// The type of the task's result, to drop it.
    pub(super) result: Type,
    /// The control block and stack the stats count.
    pub(super) bookkeeping: [i64; 2],
}

impl TaskRecord {
    fn new(root: bool, result: Type, bookkeeping: [i64; 2]) -> Self {
        TaskRecord {
            state: State::Ready,
            stack: Vec::new(),
            handlers: Vec::new(),
            kstack: effects::KStack::default(),
            unwinding: None,
            start: None,
            resume: None,
            cancelled: false,
            waiter: None,
            outcome: None,
            claimed: false,
            parent: None,
            scopes: Vec::new(),
            joined: Default::default(),
            root,
            catch_depth: 0,
            preserve: false,
            result,
            bookkeeping,
        }
    }
}

/// A channel: its messages, its capacity, and whether it is closed.
pub(super) struct Channel {
    items: VecDeque<Words>,
    capacity: usize,
    closed: bool,
}

const DEADLOCK: &str = "task scheduler deadlock: no runnable tasks and the root is blocked";

impl Machine<'_, '_> {
    /// Start the task runtime: the root task, which runs `main`.
    pub(super) fn start_tasks(&mut self) {
        let bookkeeping = self.task_bookkeeping();
        let mut root = TaskRecord::new(true, Type::Unit, bookkeeping);
        root.state = State::Running;
        self.tasks.push(root);
        self.current = 0;
    }

    /// Free the root's bookkeeping at the end of a run.
    pub(super) fn finish_tasks(&mut self) -> Run<()> {
        if let Some(root) = self.tasks.first() {
            let [block, stack] = root.bookkeeping;
            self.memory.free(block)?;
            self.memory.free(stack)?;
        }
        Ok(())
    }

    fn task_bookkeeping(&mut self) -> [i64; 2] {
        [self.memory.allocate(8, true), self.memory.allocate(8, true)]
    }

    /// Swap the current task's stacks out and `next`'s in.
    fn switch_to(&mut self, next: usize) {
        let record = &mut self.tasks[self.current];
        record.stack = std::mem::take(&mut self.stack);
        record.handlers = std::mem::take(&mut self.handlers);
        record.kstack = std::mem::take(&mut self.kstack);
        record.unwinding = self.unwinding.take();
        self.current = next;
        let record = &mut self.tasks[next];
        self.stack = std::mem::take(&mut record.stack);
        self.handlers = std::mem::take(&mut record.handlers);
        self.kstack = std::mem::take(&mut record.kstack);
        self.unwinding = record.unwinding.take();
        record.state = State::Running;
        if let Some(program) = self.stack.last().map(|frame| frame.program) {
            self.select(program);
        }
    }

    /// Run the next ready task. The run loop then enters its body or
    /// resumes its suspended operation.
    pub(super) fn schedule(&mut self) -> Run<()> {
        let Some(next) = self.ready.pop_front() else {
            return Err(Stop::Panic(Diagnostic::new(Span::default(), DEADLOCK)));
        };
        self.switch_to(next);
        Ok(())
    }

    /// The run loop's work for the current task before its next step: its
    /// body's first frame, or the rest of a suspended operation. `false`
    /// when there is none.
    pub(super) fn task_entry(&mut self) -> std::result::Result<bool, Raise> {
        let current = self.current;
        if let Some((function, environment)) = self.tasks[current].start.take() {
            let caller = Return {
                site: Site::TaskEnd,
                unwind: None,
                catch: None,
            };
            self.enter_code(function, Vec::new(), Some(caller), Some(environment))
                .map_err(Raise::Stop)?;
            return Ok(true);
        }
        let Some(resume) = self.tasks[current].resume.take() else {
            return Ok(false);
        };
        let flow =
            (resume.then)(self, Vec::new()).map_err(|stop| Raise::at(stop, resume.unwind))?;
        self.proceed(flow, resume.site, resume.unwind)?;
        Ok(true)
    }

    /// Suspend the current task until the scheduler picks it again, then go
    /// on with `then`.
    pub(super) fn suspend(
        &mut self,
        then: Then,
        site: Site,
        unwind: Option<BlockId>,
    ) -> std::result::Result<(), Raise> {
        if self.nested > 0 {
            return Err(Raise::Stop(Stop::Fault(
                "a task switch inside a runtime callback".into(),
            )));
        }
        self.tasks[self.current].resume = Some(Resume { then, site, unwind });
        self.schedule().map_err(Raise::Stop)
    }

    /// The current task's body ended: record how, wake its joiner, and run
    /// another task.
    pub(super) fn task_end(&mut self, outcome: Outcome) -> std::result::Result<(), Raise> {
        let current = self.current;
        let outcome = match outcome {
            Outcome::Completed(words, _)
                if self.tasks[current].cancelled && !self.tasks[current].preserve =>
            {
                let ty = self.tasks[current].result;
                self.drop_value(ty, &words).map_err(Raise::Stop)?;
                Outcome::Cancelled
            }
            other => other,
        };
        let record = &mut self.tasks[current];
        record.state = State::Finished;
        record.outcome = Some(outcome);
        if record.claimed {
            self.release_bookkeeping(current).map_err(Raise::Stop)?;
        }
        if let Some(waiter) = self.tasks[current].waiter.take() {
            self.tasks[waiter].state = State::Ready;
            self.ready.push_back(waiter);
        }
        self.schedule().map_err(Raise::Stop)
    }

    fn release_bookkeeping(&mut self, task: usize) -> Run<()> {
        let [block, stack] = self.tasks[task].bookkeeping;
        self.memory.free(block)?;
        self.memory.free(stack)
    }

    /// Whether a panic unwinds where it is raised: in a spawned task, or
    /// inside a `Task.catch` (in `main`, it otherwise ends the run).
    fn panic_unwinds(&self, error: &Diagnostic) -> bool {
        let task = &self.tasks[self.current];
        error.message.starts_with("panic") && (!task.root || task.catch_depth > 0)
    }

    pub(super) fn task_op(&mut self, op: TaskOp, operands: &[Operand], ty: Type) -> Run<Flow> {
        let words = operands
            .iter()
            .map(|operand| self.operand(*operand))
            .collect::<Run<Vec<_>>>()?;
        if self.tasks.is_empty() {
            return fault("a task operation without the task runtime");
        }
        match op {
            TaskOp::Spawn {
                result,
                obligation,
                parallel,
            } => Ok(Flow::Done(vec![
                self.spawn(&words[0], result, obligation, parallel)? as i64,
            ])),
            TaskOp::Yield => {
                let current = self.current;
                self.tasks[current].state = State::Ready;
                self.ready.push_back(current);
                Ok(Flow::Suspend(Box::new(|machine, _| {
                    let cancelled = machine.tasks[machine.current].cancelled;
                    Ok(Flow::Done(vec![i64::from(cancelled)]))
                })))
            }
            TaskOp::CheckCancel => Ok(Flow::Done(vec![i64::from(
                self.tasks[self.current].cancelled,
            )])),
            TaskOp::Cancel => {
                let target = self.memory.load(words[0][0], 1)?[0];
                self.cancel(target as usize);
                Ok(Flow::Done(vec![0]))
            }
            TaskOp::Join { exit, parallel } => {
                let target = words[0][0] as usize;
                self.join(
                    target,
                    Box::new(move |machine, outcome| machine.join_result(outcome, exit, parallel)),
                )
            }
            TaskOp::Scope {
                failure,
                catch,
                parallel,
            } => self.scope(&words[0], failure, catch, parallel, ty),
        }
    }

    /// `Task.spawn` / `Thread.spawn`: a new ready task running the `once`
    /// body `[code, environment]` in the innermost scope.
    fn spawn(&mut self, body: &[i64], result: Type, preserve: bool, parallel: bool) -> Run<usize> {
        let current = self.current;
        if self.tasks[current].scopes.is_empty() {
            return panic_at(
                Span::default(),
                "Task.spawn requires an enclosing Task.scope",
            );
        }
        // A thread starts with an empty handler stack; a task inherits the
        // innermost copyable frames that capture nothing.
        let handlers = if parallel {
            Vec::new()
        } else {
            self.inheritable_handlers()
        };
        let id = self.tasks.len();
        let bookkeeping = self.task_bookkeeping();
        let mut record = TaskRecord::new(false, result, bookkeeping);
        record.handlers = handlers;
        record.start = Some((code_function(body[0])?, body[1]));
        record.preserve = preserve;
        record.parent = (!parallel).then_some(current);
        self.tasks.push(record);
        self.ready.push_back(id);
        self.tasks[current]
            .scopes
            .last_mut()
            .expect("a scope")
            .push(id);
        Ok(id)
    }

    /// Structured cancellation: the target and its unfinished descendants.
    fn cancel(&mut self, target: usize) {
        if target >= self.tasks.len() {
            return;
        }
        self.tasks[target].cancelled = true;
        let mut pending = vec![target];
        while let Some(parent) = pending.pop() {
            for child in 0..self.tasks.len() {
                if self.tasks[child].parent == Some(parent)
                    && self.tasks[child].state != State::Finished
                {
                    self.tasks[child].cancelled = true;
                    pending.push(child);
                }
            }
        }
    }

    /// Join `target`: its outcome goes to `then` once it has finished,
    /// blocking the current task until then.
    fn join(&mut self, target: usize, then: OnOutcome) -> Run<Flow> {
        let failed = |message: &str| Outcome::Failed(Diagnostic::new(Span::default(), message));
        if target >= self.tasks.len() || target == 0 {
            return then(self, failed("Task.join received an invalid task handle"));
        }
        if self.tasks[target].claimed {
            return then(self, failed("task handle was already joined"));
        }
        self.tasks[target].claimed = true;
        let current = self.current;
        self.tasks[current].joined.insert(target);
        if let Some(outcome) = self.tasks[target].outcome.clone() {
            self.release_bookkeeping(target)?;
            return then(self, outcome);
        }
        self.tasks[current].state = State::Blocked;
        self.tasks[target].waiter = Some(current);
        Ok(Flow::Suspend(Box::new(move |machine, _| {
            let Some(outcome) = machine.tasks[target].outcome.clone() else {
                return fault("a joiner resumed before its task finished");
            };
            then(machine, outcome)
        })))
    }

    /// A join's value: the task's `TaskExit` (a thread's payload); its
    /// panic is raised here.
    fn join_result(&mut self, outcome: Outcome, exit: TaskExitShape, parallel: bool) -> Run<Flow> {
        Ok(match outcome {
            Outcome::Completed(words, _) if parallel => Flow::Done(words),
            Outcome::Completed(words, _) => {
                Flow::Done(self.encode_variant(exit.result, exit.completed_tag, words))
            }
            Outcome::Cancelled => {
                let payload = vec![0; self.width(exit.payload)];
                Flow::Done(self.encode_variant(exit.result, exit.cancelled_tag, payload))
            }
            Outcome::Failed(error) => Flow::Panic(error),
        })
    }

    /// `Task.scope` / `Thread.scope` / `Task.catch`: run the body, then
    /// join every child (see the module documentation).
    fn scope(
        &mut self,
        body: &[i64],
        failure: Option<crate::runtime_types::ResultShape>,
        catch: Option<crate::runtime_types::ResultShape>,
        parallel: bool,
        ty: Type,
    ) -> Run<Flow> {
        let current = self.current;
        if catch.is_some() {
            self.tasks[current].catch_depth += 1;
        }
        if self.tasks[current].scopes.len() >= 16 {
            return Err(Stop::Panic(Diagnostic::new(
                Span::default(),
                "reference task scope nesting limit exceeded (16)",
            )));
        }
        self.tasks[current].scopes.push(Vec::new());
        Ok(Flow::Call {
            function: code_function(body[0])?,
            args: Vec::new(),
            environment: Some(body[1]),
            then: Some(Box::new(move |machine, words| {
                let cancel = failure
                    .is_some_and(|shape| words.first() == Some(&(shape.err_tag as i64)))
                    && !parallel;
                if cancel {
                    machine.cancel_scope();
                }
                machine.scope_end(Box::new(move |machine, end| {
                    scope_finish(machine, ty, catch, Ok(words), end)
                }))
            })),
            catch: Some(Box::new(move |machine, error| {
                if machine.panic_unwinds(&error) && !parallel {
                    machine.cancel_scope();
                }
                machine.scope_end(Box::new(move |machine, end| {
                    scope_finish(machine, ty, catch, Err(error), end)
                }))
            })),
        })
    }

    /// The result type of a scope's body: the scope's own, or what a catch
    /// wraps.
    fn scope_body_result(
        &self,
        ty: Type,
        catch: Option<crate::runtime_types::ResultShape>,
    ) -> Type {
        match (catch, ty.layout()) {
            (Some(shape), Some(layout)) => self.program.enums[layout].variants[shape.ok_tag]
                .fields
                .first()
                .copied()
                .unwrap_or(Type::Unit),
            _ => ty,
        }
    }

    /// Cancel the unjoined children of the innermost scope.
    fn cancel_scope(&mut self) {
        let current = self.current;
        let children = self.tasks[current]
            .scopes
            .last()
            .cloned()
            .unwrap_or_default();
        for child in children {
            if !self.tasks[current].joined.contains(&child) {
                self.cancel(child);
            }
        }
    }

    /// Close the innermost scope: join its children in spawn order,
    /// dropping their results; `then` gets the first child's panic.
    fn scope_end(&mut self, then: OnEnd) -> Run<Flow> {
        let current = self.current;
        let children = self.tasks[current].scopes.pop().unwrap_or_default();
        let children = children
            .into_iter()
            .filter(|child| !self.tasks[current].joined.contains(child))
            .collect();
        join_children(self, children, None, then)
    }

    // ---- channels ----------------------------------------------------------

    /// `Channel.new(capacity)`: a counted handle naming the channel.
    pub(super) fn channel_new(&mut self, capacity: i64, span: Span) -> Run<Words> {
        if !(1..=(1 << 24)).contains(&capacity) {
            return panic_at(span, "panic: channel capacity must be between 1 and 2^24");
        }
        let handle = self.memory.allocate(8, true);
        self.memory.store(handle, &[self.channels.len() as i64])?;
        self.channels.push(Channel {
            items: VecDeque::new(),
            capacity: capacity as usize,
            closed: false,
        });
        Ok(vec![handle])
    }

    /// A send, receive or close on the channel at an element of a view: a
    /// blocked operation yields and tries again.
    pub(super) fn channel_op(
        &mut self,
        op: SliceOp,
        values: &[i64],
        element: Type,
        span: Span,
    ) -> Run<Flow> {
        let (data, length, stride) = (values[0], values[1], values[2]);
        let index = values[4];
        if !(0..length).contains(&index) {
            return panic_at(span, "panic: slice index out of bounds");
        }
        let handle = self.memory.load(data + index * stride, 1)?[0];
        let channel = self.memory.load(handle, 1)?[0] as usize;
        let Type::Channel(message) = element else {
            return fault("a channel operation on a view of non-channels");
        };
        let width = self.width(self.program.pointees[message]);
        let message = values.get(5..5 + width).map(<[i64]>::to_vec);
        channel_try(self, op, channel, message, span)
    }
}

impl Machine<'_, '_> {
    /// `kush_sys_wait_ready` outside check mode (WEB-REACTOR's deterministic
    /// model, as on the tree): in a task, poll the descriptor for up to 1 ms
    /// at a time and yield in between, so waiting tasks are polled in
    /// ready-queue order; without tasks, a plain poll.
    pub(super) fn wait_ready(&mut self, foreign: usize, values: &[i64], ty: Type) -> Run<Flow> {
        let program = self.program.clone();
        let Some(shape) = program.foreign_functions[foreign]
            .as_ref()
            .and_then(|function| function.fallible)
        else {
            return fault("kush_sys_wait_ready without a Result");
        };
        let (fd, events, timeout) = (values[0], values[1], values[2]);
        if !(-1..=i64::from(i32::MAX)).contains(&timeout) {
            return Ok(Flow::Done(status_words(self, shape, (22, 0), ty)));
        }
        if self.tasks.is_empty() {
            let result = if fd >= 0 {
                crate::host::eval_poll(&self.system.files, fd, events, timeout)
            } else {
                loop {
                    let wait = if timeout < 0 { 1000 } else { timeout as u64 };
                    std::thread::sleep(std::time::Duration::from_millis(wait));
                    if timeout >= 0 {
                        break (0, 0);
                    }
                }
            };
            return Ok(Flow::Done(status_words(self, shape, result, ty)));
        }
        let deadline = (timeout >= 0)
            .then(|| std::time::Instant::now() + std::time::Duration::from_millis(timeout as u64));
        wait_step(self, fd, events, deadline, events & 256 != 0, shape, ty)
    }
}

/// A host result's words: `Ok(value)` or `Err(status)`.
fn status_words(
    machine: &Machine<'_, '_>,
    shape: crate::runtime_types::ResultShape,
    (status, value): (i64, i64),
    ty: Type,
) -> Words {
    let words = if status == 0 {
        vec![shape.ok_tag as i64, value]
    } else {
        vec![shape.err_tag as i64, status]
    };
    fit(words, machine.width(ty))
}

/// One poll of a task's `kush_sys_wait_ready`; it yields between polls.
fn wait_step(
    machine: &mut Machine<'_, '_>,
    fd: i64,
    events: i64,
    deadline: Option<std::time::Instant>,
    shielded: bool,
    shape: crate::runtime_types::ResultShape,
    ty: Type,
) -> Run<Flow> {
    let done = |machine: &Machine<'_, '_>, result| {
        Ok(Flow::Done(status_words(machine, shape, result, ty)))
    };
    if !shielded && machine.tasks[machine.current].cancelled {
        return done(machine, (125, 0)); // ECANCELED
    }
    let left =
        deadline.map(|deadline| deadline.saturating_duration_since(std::time::Instant::now()));
    let slice = left.map_or(1, |left| left.as_millis().min(1) as i64);
    let result = if fd >= 0 {
        crate::host::eval_poll(&machine.system.files, fd, events, slice)
    } else {
        std::thread::sleep(std::time::Duration::from_millis(slice as u64));
        (0, 0)
    };
    if result != (0, 0) {
        return done(machine, result);
    }
    if deadline.is_some_and(|deadline| std::time::Instant::now() >= deadline) {
        return done(machine, (0, 0));
    }
    let current = machine.current;
    machine.tasks[current].state = State::Ready;
    machine.ready.push_back(current);
    Ok(Flow::Suspend(Box::new(move |machine, _| {
        wait_step(machine, fd, events, deadline, shielded, shape, ty)
    })))
}

/// A scope's value once its children are joined: the body's result, or the
/// panic of the body or a child (`end`); a catch makes them `Ok` / `Err`.
fn scope_finish(
    machine: &mut Machine<'_, '_>,
    ty: Type,
    catch: Option<crate::runtime_types::ResultShape>,
    result: std::result::Result<Words, Diagnostic>,
    end: Option<Diagnostic>,
) -> Run<Flow> {
    let outcome = match (result, end) {
        (Ok(words), None) => Ok(words),
        (Err(error), _) => Err(error),
        (Ok(words), Some(error)) => {
            let body_ty = machine.scope_body_result(ty, catch);
            machine.drop_value(body_ty, &words)?;
            Err(error)
        }
    };
    let Some(shape) = catch else {
        return Ok(match outcome {
            Ok(words) => Flow::Done(words),
            Err(error) => Flow::Panic(error),
        });
    };
    let current = machine.current;
    machine.tasks[current].catch_depth -= 1;
    Ok(match outcome {
        Ok(words) => Flow::Done(machine.encode_variant(ty, shape.ok_tag, words)),
        Err(error) if error.message.starts_with("panic") => {
            Flow::Done(machine.encode_variant(ty, shape.err_tag, Vec::new()))
        }
        Err(error) => Flow::Panic(error),
    })
}

/// One attempt at a channel operation; a blocked one yields and retries.
fn channel_try(
    machine: &mut Machine<'_, '_>,
    op: SliceOp,
    channel: usize,
    message: Option<Words>,
    span: Span,
) -> Run<Flow> {
    let state = &mut machine.channels[channel];
    let done = match op {
        SliceOp::ChannelClose => {
            state.closed = true;
            Some(vec![0])
        }
        SliceOp::ChannelSend if state.closed => {
            return panic_at(span, "panic: send on a closed channel");
        }
        SliceOp::ChannelSend if state.items.len() < state.capacity => {
            state.items.push_back(message.clone().unwrap_or_default());
            Some(vec![0])
        }
        SliceOp::ChannelRecv {
            some_tag,
            none_tag,
            option,
        } => match state.items.pop_front() {
            Some(item) => Some(machine.encode_variant(Type::Enum(option), some_tag, item)),
            None if state.closed => {
                Some(machine.encode_variant(Type::Enum(option), none_tag, Vec::new()))
            }
            None => None,
        },
        _ => None,
    };
    if let Some(words) = done {
        return Ok(Flow::Done(words));
    }
    let current = machine.current;
    machine.tasks[current].state = State::Ready;
    machine.ready.push_back(current);
    Ok(Flow::Suspend(Box::new(move |machine, _| {
        channel_try(machine, op, channel, message, span)
    })))
}

/// Join a scope's children one after another (each join may block).
fn join_children(
    machine: &mut Machine<'_, '_>,
    mut children: VecDeque<usize>,
    failure: Option<Diagnostic>,
    then: OnEnd,
) -> Run<Flow> {
    let Some(child) = children.pop_front() else {
        return then(machine, failure);
    };
    machine.join(
        child,
        Box::new(move |machine, outcome| {
            let mut failure = failure;
            match outcome {
                Outcome::Completed(_, true) => {
                    return Err(Stop::Panic(Diagnostic::new(
                        Span::default(),
                        "internal error: an unjoined task result carrying a linear obligation reached the scope epilogue; join it explicitly before the scope ends",
                    )));
                }
                Outcome::Completed(words, false) => {
                    let ty = machine.tasks[child].result;
                    machine.drop_value(ty, &words)?;
                }
                Outcome::Cancelled => {}
                Outcome::Failed(error) => {
                    failure.get_or_insert(error);
                }
            }
            join_children(machine, children, failure, then)
        }),
    )
}
