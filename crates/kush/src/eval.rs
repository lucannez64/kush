//! Bounded reference evaluator for checked executable IR. It shares no
//! execution logic with the native backend; tests compare the two.
use crate::grades::Grade;
use crate::{Diagnostic, Span, executable::*, lexer::Kind, runtime_types::ResultShape};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    io::{self, Cursor, Read, Write},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
    },
    thread,
};
type Result<T> = std::result::Result<T, Diagnostic>;
impl Executable {
    /// Bounded reference evaluator; native execution does not have this budget.
    pub fn evaluate(&self, output: &mut dyn Write) -> Result<i64> {
        self.evaluate_with_stats(output).map(|(value, _)| value)
    }
    pub fn evaluate_with_stats(&self, output: &mut dyn Write) -> Result<(i64, MemoryStats)> {
        self.evaluate_with_io_and_stats(&mut io::empty(), output)
    }
    /// Reference evaluation with explicit standard-stream implementations.
    pub fn evaluate_with_io(&self, input: &mut dyn Read, output: &mut dyn Write) -> Result<i64> {
        self.evaluate_with_io_and_stats(input, output)
            .map(|(value, _)| value)
    }
    pub fn evaluate_with_io_and_stats(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
    ) -> Result<(i64, MemoryStats)> {
        self.evaluate_with_io_limits(input, output, None)
    }
    /// Reference evaluation with a deterministic budget for **fallible**
    /// allocation attempts. Normal allocation is unaffected. A budget of zero
    /// makes `Box.try_new`, a growth-capable `Box.try_reuse`, and
    /// `Bytes.try_with_capacity` fail with their checked error value. This is
    /// a test/tooling probe for failure paths, not a language effect or a
    /// native allocator limit.
    pub fn evaluate_with_alloc_budget(
        &self,
        output: &mut dyn Write,
        budget: usize,
    ) -> Result<(i64, MemoryStats)> {
        self.evaluate_with_io_limits(&mut io::empty(), output, Some(budget))
    }
    fn evaluate_with_io_limits(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        alloc_budget: Option<usize>,
    ) -> Result<(i64, MemoryStats)> {
        if self.uses_tasks {
            return self.evaluate_tasks(input, output, alloc_budget);
        }
        let entry = self.entry()?;
        let heap = SharedHeap::new();
        let stats = StatsHandle::new(self.fusions);
        let mut evaluator = Evaluator {
            program: self,
            input,
            output,
            fuel: 100_000,
            depth: 0,
            heap: heap.clone(),
            stats: stats.clone(),
            task: None,
            try_budget: alloc_budget.map(|budget| Arc::new(AtomicUsize::new(budget))),
        };
        let result = evaluator.call(entry, vec![])?.scalar();
        if heap.len() != 0 {
            return Err(Diagnostic::new(
                Span::default(),
                "internal ownership error: live owning allocations after normal program exit",
            ));
        }
        Ok((result, stats.snapshot()))
    }
    /// Cooperative reference scheduler. Each task is an OS thread used only as
    /// a stack; strict handoff ensures exactly one task evaluates at a time.
    /// Host I/O is buffered so no non-`Send` I/O trait object crosses a thread.
    fn evaluate_tasks(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        alloc_budget: Option<usize>,
    ) -> Result<(i64, MemoryStats)> {
        let entry = self.entry()?;
        let mut bytes = Vec::new();
        input
            .read_to_end(&mut bytes)
            .map_err(|e| Diagnostic::new(Span::default(), format!("input failed: {e}")))?;
        let heap = SharedHeap::new();
        let stats = StatsHandle::new(self.fusions);
        let source = SharedInput(Arc::new(Mutex::new(Cursor::new(bytes))));
        let sink = SharedWriter(Arc::new(Mutex::new(Vec::new())));
        let result = self.run_scheduler(
            entry,
            heap.clone(),
            stats.clone(),
            source,
            sink.clone(),
            alloc_budget.map(|budget| Arc::new(AtomicUsize::new(budget))),
        );
        let output_bytes = std::mem::take(&mut *sink.0.lock().unwrap());
        output
            .write_all(&output_bytes)
            .map_err(|e| Diagnostic::new(Span::default(), format!("output failed: {e}")))?;
        let result = result?;
        if heap.len() != 0 {
            return Err(Diagnostic::new(
                Span::default(),
                "internal ownership error: live owning allocations after normal task exit",
            ));
        }
        Ok((result, stats.snapshot()))
    }
    fn run_scheduler(
        &self,
        entry: usize,
        heap: SharedHeap,
        stats: StatsHandle,
        source: SharedInput,
        sink: SharedWriter,
        try_budget: Option<Arc<AtomicUsize>>,
    ) -> Result<i64> {
        let mut records: Vec<TaskRecord> = Vec::new();
        let mut ready: VecDeque<usize> = VecDeque::new();
        let mut current: Option<usize> = None;
        let result = thread::scope(|scope| -> Result<i64> {
            let root = self.start_task(
                scope,
                &mut records,
                &heap,
                &stats,
                &source,
                &sink,
                &try_budget,
                entry,
                None,
                Vec::new(),
                false,
            );
            ready.push_back(root);
            loop {
                if current.is_none() {
                    let Some(id) = ready.pop_front() else {
                        for record in records.iter_mut() {
                            let _ = record.commands.send(TaskCommand::Stop);
                        }
                        return Err(Diagnostic::new(
                            Span::default(),
                            "task scheduler deadlock: no runnable tasks and the root is blocked",
                        ));
                    };
                    records[id].state = TaskState::Running;
                    let command = records[id].pending.take().unwrap_or(TaskCommand::Run);
                    let _ = records[id].commands.send(command);
                    current = Some(id);
                }
                let id = current.unwrap();
                let event = records[id]
                    .events
                    .recv()
                    .map_err(|_| Diagnostic::new(Span::default(), "task thread disconnected"))?;
                match event {
                    TaskEvent::Yield => {
                        records[id].state = TaskState::Ready;
                        ready.push_back(id);
                        current = None;
                    }
                    TaskEvent::Spawn {
                        function,
                        environment,
                        preserve,
                    } => {
                        let child = self.start_task(
                            scope,
                            &mut records,
                            &heap,
                            &stats,
                            &source,
                            &sink,
                            &try_budget,
                            function,
                            environment,
                            Vec::new(),
                            preserve,
                        );
                        let _ = records[id].commands.send(TaskCommand::Spawned(child));
                        records[child].state = TaskState::Ready;
                        ready.push_back(child);
                    }
                    TaskEvent::Join(target) => {
                        if target >= records.len() {
                            let _ = records[id].commands.send(TaskCommand::Joined(
                                TaskOutcome::Failed(Diagnostic::new(
                                    Span::default(),
                                    "Task.join received an invalid task handle",
                                )),
                            ));
                            continue;
                        }
                        if records[target].claimed {
                            let _ = records[id].commands.send(TaskCommand::Joined(
                                TaskOutcome::Failed(Diagnostic::new(
                                    Span::default(),
                                    "task handle was already joined",
                                )),
                            ));
                            continue;
                        }
                        records[target].claimed = true;
                        if let Some(outcome) = records[target].outcome.clone() {
                            stats.deallocation();
                            stats.deallocation();
                            let _ = records[id].commands.send(TaskCommand::Joined(outcome));
                        } else {
                            records[id].state = TaskState::Blocked;
                            records[target].waiter = Some(id);
                            current = None;
                        }
                    }
                    TaskEvent::Cancel(target) => {
                        if target < records.len() {
                            records[target].cancelled.store(true, Ordering::Relaxed);
                        }
                    }
                    TaskEvent::Done(outcome) => {
                        records[id].state = TaskState::Finished;
                        records[id].outcome = Some(outcome.clone());
                        if records[id].claimed {
                            stats.deallocation();
                            stats.deallocation();
                        }
                        if let Some(waiter) = records[id].waiter.take() {
                            records[waiter].pending = Some(TaskCommand::Joined(outcome));
                            records[waiter].state = TaskState::Ready;
                            ready.push_back(waiter);
                        }
                        current = None;
                        if id == 0 {
                            for (other, record) in records.iter_mut().enumerate() {
                                if other != 0 && record.state != TaskState::Finished {
                                    let _ = record.commands.send(TaskCommand::Stop);
                                }
                            }
                            return Ok(0);
                        }
                    }
                }
            }
        });
        stats.deallocation();
        stats.deallocation();
        let root = records.first().and_then(|record| record.outcome.clone());
        match root {
            Some(TaskOutcome::Completed(value, _)) => {
                let mut evaluator = Evaluator {
                    program: self,
                    input: source,
                    output: sink,
                    fuel: 100_000,
                    depth: 0,
                    heap,
                    stats,
                    task: None,
                    try_budget: try_budget.clone(),
                };
                let scalar = value.scalar();
                evaluator.drop_value(value)?;
                Ok(scalar)
            }
            Some(TaskOutcome::Cancelled) => Err(Diagnostic::new(
                Span::default(),
                "the root task was cancelled",
            )),
            Some(TaskOutcome::Failed(error)) => Err(error),
            None => result,
        }
    }
    #[allow(clippy::too_many_arguments)]
    fn start_task<'scope>(
        &'scope self,
        scope: &'scope thread::Scope<'scope, '_>,
        records: &mut Vec<TaskRecord>,
        heap: &SharedHeap,
        stats: &StatsHandle,
        source: &SharedInput,
        sink: &SharedWriter,
        try_budget: &Option<Arc<AtomicUsize>>,
        function: usize,
        environment: Option<usize>,
        arguments: Vec<Value>,
        preserve: bool,
    ) -> usize {
        let id = records.len();
        let (commands, command_receiver) = mpsc::channel();
        let (event_sender, events) = mpsc::channel();
        let cancelled = Arc::new(AtomicBool::new(false));
        let comm = TaskComm {
            events: event_sender,
            commands: command_receiver,
            cancelled: cancelled.clone(),
            scopes: Vec::new(),
            joined: BTreeSet::new(),
        };
        let evaluator = Evaluator {
            program: self,
            input: source.clone(),
            output: sink.clone(),
            fuel: 100_000,
            depth: 0,
            heap: heap.clone(),
            stats: stats.clone(),
            task: Some(comm),
            try_budget: try_budget.clone(),
        };
        stats.allocation();
        stats.allocation();
        let _ = scope.spawn(move || {
            let mut evaluator = evaluator;
            match evaluator.task.as_mut().unwrap().commands.recv() {
                Ok(TaskCommand::Run) => {}
                _ => return,
            }
            let captures = match environment {
                Some(environment) => match evaluator.heap.take(environment) {
                    Some(Value::Closure { captures }) => {
                        evaluator.stats.deallocation();
                        captures
                    }
                    _ => Vec::new(),
                },
                None => Vec::new(),
            };
            let outcome = match evaluator.call_with(function, captures, arguments) {
                Ok(value) => {
                    if evaluator
                        .task
                        .as_ref()
                        .is_some_and(|task| task.cancelled.load(Ordering::Relaxed))
                    {
                        if preserve {
                            // A completed payload with an owning/linear
                            // obligation is transferred to the joiner instead
                            // of being discarded.
                            TaskOutcome::Completed(value, true)
                        } else {
                            match evaluator.drop_value(value) {
                                Ok(()) => TaskOutcome::Cancelled,
                                Err(error) => TaskOutcome::Failed(error),
                            }
                        }
                    } else {
                        TaskOutcome::Completed(value, preserve)
                    }
                }
                Err(error) => TaskOutcome::Failed(error),
            };
            let _ = evaluator
                .task
                .as_ref()
                .unwrap()
                .events
                .send(TaskEvent::Done(outcome));
        });
        records.push(TaskRecord {
            state: TaskState::Ready,
            commands,
            events,
            cancelled,
            waiter: None,
            outcome: None,
            claimed: false,
            pending: None,
        });
        id
    }
}

fn io_error_code(error: &io::Error) -> i64 {
    // Injected readers/writers may have no platform errno; map those to Linux EIO.
    error
        .raw_os_error()
        .filter(|code| *code > 0)
        .map_or(5, i64::from)
}
#[derive(Debug, Clone, Copy, Default, PartialEq, Eq)]
pub struct MemoryStats {
    pub allocations: usize,
    pub deallocations: usize,
    pub peak_live: usize,
    /// Successful capacity growths of byte buffers and vectors. Reallocation
    /// replaces storage, so it is not counted as an allocation/free pair.
    pub buffer_growths: usize,
    /// Successful checked `Box.reuse` operations that kept their allocation.
    pub reuses: usize,
    /// Checked nested in-place map fusions selected by the compiler.
    pub fusions: usize,
}
impl MemoryStats {
    /// Stable user-facing diagnostics line. It is written to stderr by the
    /// CLI and is a tooling observation, not a source-language effect.
    pub fn report(&self) -> String {
        format!(
            "allocation-stats: allocations={} deallocations={} peak-live={} buffer-growths={} reuses={} fusions={}",
            self.allocations,
            self.deallocations,
            self.peak_live,
            self.buffer_growths,
            self.reuses,
            self.fusions
        )
    }
}
#[derive(Debug, Clone)]
struct HeapState {
    map: BTreeMap<usize, Value>,
    next: usize,
}
/// A heap shared by every task in one reference evaluation. Only one task runs
/// at a time under the reference scheduler, so this is a strict-handoff store,
/// not a parallel-memory claim.
#[derive(Clone)]
struct SharedHeap(Arc<Mutex<HeapState>>);
impl SharedHeap {
    fn new() -> Self {
        Self(Arc::new(Mutex::new(HeapState {
            map: BTreeMap::new(),
            next: 0,
        })))
    }
    fn allocate(&self, value: Value) -> usize {
        let mut state = self.0.lock().unwrap();
        let id = state.next;
        state.next += 1;
        state.map.insert(id, value);
        id
    }
    fn insert(&self, id: usize, value: Value) {
        self.0.lock().unwrap().map.insert(id, value);
    }
    fn take(&self, id: usize) -> Option<Value> {
        self.0.lock().unwrap().map.remove(&id)
    }
    fn get(&self, id: usize) -> Option<Value> {
        self.0.lock().unwrap().map.get(&id).cloned()
    }
    fn len(&self) -> usize {
        self.0.lock().unwrap().map.len()
    }
}
#[derive(Debug)]
struct StatsState {
    stats: MemoryStats,
    live: usize,
}
/// Shared allocation diagnostics. Task stacks/control blocks are charged as
/// allocations even though the reference runtime uses OS threads.
#[derive(Clone)]
struct StatsHandle(Arc<Mutex<StatsState>>);
impl StatsHandle {
    fn new(fusions: usize) -> Self {
        Self(Arc::new(Mutex::new(StatsState {
            stats: MemoryStats {
                fusions,
                ..MemoryStats::default()
            },
            live: 0,
        })))
    }
    fn allocation(&self) {
        let mut state = self.0.lock().unwrap();
        state.stats.allocations += 1;
        state.live += 1;
        state.stats.peak_live = state.stats.peak_live.max(state.live);
    }
    fn deallocation(&self) {
        let mut state = self.0.lock().unwrap();
        state.stats.deallocations += 1;
        state.live = state.live.saturating_sub(1);
    }
    fn growth(&self) {
        self.0.lock().unwrap().stats.buffer_growths += 1;
    }
    fn reuse(&self) {
        self.0.lock().unwrap().stats.reuses += 1;
    }
    fn snapshot(&self) -> MemoryStats {
        self.0.lock().unwrap().stats
    }
}
#[derive(Clone)]
struct SharedInput(Arc<Mutex<Cursor<Vec<u8>>>>);
impl Read for SharedInput {
    fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
        self.0.lock().unwrap().read(destination)
    }
}
#[derive(Clone)]
struct SharedWriter(Arc<Mutex<Vec<u8>>>);
impl Write for SharedWriter {
    fn write(&mut self, source: &[u8]) -> io::Result<usize> {
        self.0.lock().unwrap().extend_from_slice(source);
        Ok(source.len())
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
#[derive(Debug, Default)]
struct ArenaState {
    slots: Vec<Option<Value>>,
    /// One owner plus one reference per live `ArenaBox`.
    references: usize,
}
#[derive(Debug, Clone)]
enum Value {
    Scalar(i64),
    Enum {
        tag: usize,
        fields: Vec<Value>,
    },
    Owned(usize),
    Borrowed(usize),
    /// An owning bump-allocator region handle. Payloads live in `slots`; every
    /// `ArenaBox` keeps one explicit region reference and destroys its own
    /// payload exactly once.
    Arena {
        state: Arc<Mutex<ArenaState>>,
    },
    ArenaBox {
        state: Arc<Mutex<ArenaState>>,
        slot: usize,
    },
    /// A call-scoped `&Arena` borrow. It owns no reference.
    ArenaRef(Arc<Mutex<ArenaState>>),
    /// A call-scoped `&ArenaBox<T>` borrow. It owns no reference.
    ArenaBoxRef {
        state: Arc<Mutex<ArenaState>>,
        slot: usize,
    },
    Buffer {
        data: Vec<u8>,
        capacity: usize,
    },
    Vector {
        items: Vec<Value>,
        capacity: usize,
    },
    /// An immutable or exclusive slice view: `start` is in elements of the
    /// underlying storage. `array` is a shared cell used when the base is an
    /// inline array local, so writes through `&mut [T]` are visible to the
    /// owner. The base is a borrowed Vec/Bytes handle and is never itself a
    /// `Slice` (sub-slices are flattened).
    Slice {
        base: Box<Value>,
        start: usize,
        len: usize,
        array: Option<Arc<Mutex<Value>>>,
    },
    /// An inline array local whose storage has been pinned in a shared cell so
    /// a mutable slice view can alias it. Reads materialize a fresh array value.
    ArrayCell(Arc<Mutex<Value>>),
    /// A nominal-record local promoted to shared storage so a call-scoped
    /// `&Record`/`&mut Record` can point at it. Reads materialize the current
    /// record value; writes through an exclusive reference update this cell.
    RecordCell(Arc<Mutex<Value>>),
    /// A checked call-scoped record reference. It aliases the owning local's
    /// pinned cell and never owns the record or its fields.
    RecordRef(Arc<Mutex<Value>>),
    /// One normalized heterogeneous union alternative. Only the active
    /// alternative owns resources; dropping a union drops just this payload.
    Union {
        tag: usize,
        value: Box<Value>,
    },
    /// A first-class callable. `environment` is an owned closure environment
    /// for a once-consuming capturing closure, and `None` for a noncapturing
    /// function pointer.
    Function {
        function: usize,
        environment: Option<usize>,
    },
    /// Captured values stored in a closure environment. The environment cell is
    /// freed when the callable is called or dropped.
    Closure {
        captures: Vec<Value>,
    },
    /// An opaque structured-task handle. The handle owns no heap cell; scope
    /// completion joins the child exactly once.
    Task(usize),
    /// A temporary `&Task<T>` borrow used only by `Task.cancel`.
    TaskRef(usize),
}
impl Value {
    fn scalar(&self) -> i64 {
        if let Self::Scalar(value) = self {
            *value
        } else {
            unreachable!("scalar operand checked")
        }
    }
}
#[derive(Debug)]
enum Flow {
    Value(Value),
    Return(Value),
    Break(Value),
    Continue,
}
struct Frame {
    function: usize,
    locals: Vec<Value>,
    resources: Vec<Option<Value>>,
}
#[derive(Debug, Clone)]
enum TaskOutcome {
    Completed(Value, bool),
    Cancelled,
    Failed(Diagnostic),
}
#[derive(Debug)]
enum TaskEvent {
    Yield,
    Spawn {
        function: usize,
        environment: Option<usize>,
        preserve: bool,
    },
    Join(usize),
    Cancel(usize),
    Done(TaskOutcome),
}
#[derive(Debug)]
enum TaskCommand {
    Run,
    Spawned(usize),
    Joined(TaskOutcome),
    Stop,
}
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum TaskState {
    Ready,
    Running,
    Blocked,
    Finished,
}
struct TaskRecord {
    state: TaskState,
    commands: Sender<TaskCommand>,
    events: Receiver<TaskEvent>,
    cancelled: Arc<AtomicBool>,
    waiter: Option<usize>,
    outcome: Option<TaskOutcome>,
    claimed: bool,
    pending: Option<TaskCommand>,
}
struct ScopeFrame {
    children: Vec<usize>,
}
/// The channel endpoint owned by one task. `Task.yield`/`join`/`spawn` block
/// here while the scheduler runs other tasks.
struct TaskComm {
    events: Sender<TaskEvent>,
    commands: Receiver<TaskCommand>,
    cancelled: Arc<AtomicBool>,
    scopes: Vec<ScopeFrame>,
    joined: BTreeSet<usize>,
}
impl TaskComm {
    fn yield_now(&mut self) -> Result<bool> {
        self.events
            .send(TaskEvent::Yield)
            .map_err(|_| Diagnostic::new(Span::default(), "task scheduler disconnected"))?;
        match self.commands.recv() {
            Ok(TaskCommand::Run) => Ok(self.cancelled.load(Ordering::Relaxed)),
            _ => Err(Diagnostic::new(
                Span::default(),
                "task scheduler disconnected while yielding",
            )),
        }
    }
    fn spawn(
        &mut self,
        function: usize,
        environment: Option<usize>,
        preserve: bool,
    ) -> Result<usize> {
        let Some(scope) = self.scopes.last_mut() else {
            return Err(Diagnostic::new(
                Span::default(),
                "Task.spawn requires an enclosing Task.scope",
            ));
        };
        self.events
            .send(TaskEvent::Spawn {
                function,
                environment,
                preserve,
            })
            .map_err(|_| Diagnostic::new(Span::default(), "task scheduler disconnected"))?;
        match self.commands.recv() {
            Ok(TaskCommand::Spawned(id)) => {
                scope.children.push(id);
                Ok(id)
            }
            _ => Err(Diagnostic::new(
                Span::default(),
                "task scheduler disconnected while spawning",
            )),
        }
    }
    fn join(&mut self, target: usize) -> Result<TaskOutcome> {
        self.events
            .send(TaskEvent::Join(target))
            .map_err(|_| Diagnostic::new(Span::default(), "task scheduler disconnected"))?;
        match self.commands.recv() {
            Ok(TaskCommand::Joined(outcome)) => {
                self.joined.insert(target);
                Ok(outcome)
            }
            _ => Err(Diagnostic::new(
                Span::default(),
                "task scheduler disconnected while joining",
            )),
        }
    }
    fn cancel(&mut self, target: usize) -> Result<()> {
        self.events
            .send(TaskEvent::Cancel(target))
            .map_err(|_| Diagnostic::new(Span::default(), "task scheduler disconnected"))
    }
    fn check_cancel(&self) -> bool {
        self.cancelled.load(Ordering::Relaxed)
    }
    fn cancel_scope(&mut self) -> Result<()> {
        let Some(frame) = self.scopes.last() else {
            return Err(Diagnostic::new(
                Span::default(),
                "internal error: Task.scope cancellation without a scope frame",
            ));
        };
        for id in frame.children.clone() {
            if !self.joined.contains(&id) {
                self.cancel(id)?;
            }
        }
        Ok(())
    }
    fn scope_begin(&mut self) -> Result<()> {
        if self.scopes.len() >= 16 {
            return Err(Diagnostic::new(
                Span::default(),
                "reference task scope nesting limit exceeded (16)",
            ));
        }
        self.scopes.push(ScopeFrame {
            children: Vec::new(),
        });
        Ok(())
    }
    fn scope_children(&mut self) -> Result<Vec<usize>> {
        let Some(frame) = self.scopes.pop() else {
            return Err(Diagnostic::new(
                Span::default(),
                "internal error: Task.scope epilogue without a scope frame",
            ));
        };
        Ok(frame
            .children
            .into_iter()
            .filter(|id| !self.joined.contains(id))
            .collect())
    }
}
struct Evaluator<'a, R: Read, W: Write> {
    program: &'a Executable,
    input: R,
    output: W,
    fuel: usize,
    depth: usize,
    heap: SharedHeap,
    stats: StatsHandle,
    task: Option<TaskComm>,
    /// Remaining successful fallible allocation attempts for deterministic
    /// failure probes. `None` means unlimited.
    try_budget: Option<Arc<AtomicUsize>>,
}
macro_rules! value {
    ($e:expr) => {
        match $e? {
            Flow::Value(v) => v,
            returned => return Ok(returned),
        }
    };
}
impl<R: Read, W: Write> Evaluator<'_, R, W> {
    fn allocate(&mut self, payload: Value) -> Value {
        let id = self.heap.allocate(payload);
        self.stats.allocation();
        Value::Owned(id)
    }
    fn arena_new_value(&mut self) -> Value {
        self.stats.allocation();
        Value::Arena {
            state: Arc::new(Mutex::new(ArenaState {
                slots: Vec::new(),
                references: 1,
            })),
        }
    }
    fn arena_allocate(&mut self, state: &Arc<Mutex<ArenaState>>, payload: Value) -> Value {
        let mut arena = state.lock().unwrap();
        let slot = arena.slots.len();
        arena.slots.push(Some(payload));
        arena.references += 1;
        Value::ArenaBox {
            state: state.clone(),
            slot,
        }
    }
    /// Drop one region reference. The last reference releases the region's
    /// logical allocation and any payload still stored in it.
    fn arena_release(&mut self, state: &Arc<Mutex<ArenaState>>) -> Result<()> {
        let remaining = {
            let mut arena = state.lock().unwrap();
            if arena.references == 0 {
                return Err(Diagnostic::new(
                    Span::default(),
                    "internal ownership error: arena reference underflow",
                ));
            }
            arena.references -= 1;
            (arena.references == 0).then(|| arena.slots.drain(..).flatten().collect::<Vec<Value>>())
        };
        if let Some(remaining) = remaining {
            self.stats.deallocation();
            for value in remaining {
                self.drop_value(value)?;
            }
        }
        Ok(())
    }
    /// Consume one unit of the deterministic fallible-allocation budget.
    /// Without an explicit budget, fallible allocations always succeed.
    fn try_charge(&self) -> bool {
        let Some(budget) = &self.try_budget else {
            return true;
        };
        budget
            .try_update(Ordering::SeqCst, Ordering::SeqCst, |remaining| {
                remaining.checked_sub(1)
            })
            .is_ok()
    }
    /// Read an inline-array local. A pinned cell is cloned so ordinary array
    /// values keep copy semantics; views retain the shared cell identity.
    /// A grade-zero binding is never materialized: its initializer still runs
    /// for strict effects, but the reference frame never stores, activates, or
    /// reads it.
    fn erased_local(&self, slot: usize, frame: &Frame) -> bool {
        self.program.functions[frame.function].locals[slot]
            .grade
            .is_some_and(Grade::is_zero)
    }
    fn store_local(&self, slot: usize, value: Value, frame: &mut Frame) {
        let value = self.materialize(value);
        match &frame.locals[slot] {
            Value::ArrayCell(cell) | Value::RecordCell(cell) => {
                *cell.lock().unwrap() = value;
            }
            _ => frame.locals[slot] = value,
        }
    }
    fn materialize(&self, value: Value) -> Value {
        match value {
            Value::ArrayCell(cell) | Value::RecordCell(cell) => cell.lock().unwrap().clone(),
            value => value,
        }
    }
    fn buffer(&self, reference: &Value, span: Span) -> Result<(usize, Vec<u8>, usize)> {
        let Value::Borrowed(id) = reference else {
            unreachable!()
        };
        let Some(Value::Buffer { data, capacity }) = self.heap.get(*id) else {
            return Err(Diagnostic::new(
                span,
                "internal ownership error: dangling byte buffer",
            ));
        };
        Ok((*id, data, capacity))
    }
    fn bytes_call(&mut self, op: BytesOp, args: Vec<Value>, span: Span) -> Result<Value> {
        // The reference evaluator bounds host storage separately from native allocation.
        const LIMIT: usize = 16 * 1024 * 1024;
        let failure = |message| Diagnostic::new(span, message);
        match op {
            BytesOp::Clear => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Buffer { mut data, capacity }) = self.heap.take(id) else {
                    unreachable!()
                };
                data.clear();
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(Value::Owned(id))
            }
            BytesOp::WithCapacity => {
                let capacity = usize::try_from(args[0].scalar())
                    .map_err(|_| failure("panic: negative byte buffer capacity"))?;
                if capacity > LIMIT {
                    return Err(failure(
                        "reference byte-buffer capacity budget exhausted (16 MiB)",
                    ));
                }
                let mut data = Vec::new();
                data.try_reserve_exact(capacity)
                    .map_err(|_| failure("panic: byte buffer allocation failed"))?;
                Ok(self.allocate(Value::Buffer { data, capacity }))
            }
            BytesOp::Len | BytesOp::Capacity | BytesOp::Get | BytesOp::Copy => {
                let (_, data, capacity) = self.buffer(&args[0], span)?;
                match op {
                    BytesOp::Len => Ok(Value::Scalar(data.len() as i64)),
                    BytesOp::Capacity => Ok(Value::Scalar(capacity as i64)),
                    BytesOp::Get => {
                        let index = usize::try_from(args[1].scalar())
                            .map_err(|_| failure("panic: byte buffer index out of bounds"))?;
                        Ok(Value::Scalar(i64::from(*data.get(index).ok_or_else(
                            || failure("panic: byte buffer index out of bounds"),
                        )?)))
                    }
                    _ => {
                        let data = data.clone();
                        let capacity = data.len();
                        Ok(self.allocate(Value::Buffer { data, capacity }))
                    }
                }
            }
            BytesOp::Push | BytesOp::PushReserved => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let byte = u8::try_from(args[1].scalar())
                    .map_err(|_| failure("panic: byte value must be in 0..255"))?;
                let Some(Value::Buffer {
                    mut data,
                    mut capacity,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: moved byte buffer"));
                };
                if data.len() == capacity {
                    if op == BytesOp::PushReserved {
                        return Err(failure("panic: reserved byte buffer is full"));
                    }
                    let next = if capacity == 0 {
                        8
                    } else {
                        capacity
                            .checked_mul(2)
                            .ok_or_else(|| failure("panic: capacity overflow"))?
                    };
                    if next > LIMIT {
                        return Err(failure(
                            "reference byte-buffer capacity budget exhausted (16 MiB)",
                        ));
                    }
                    data.try_reserve_exact(next - data.len())
                        .map_err(|_| failure("panic: byte buffer allocation failed"))?;
                    capacity = next;
                    self.stats.growth();
                }
                data.push(byte);
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(Value::Owned(id))
            }
        }
    }
    fn string_call(&mut self, op: StringOp, args: Vec<Value>, span: Span) -> Result<Value> {
        let failure = |message| Diagnostic::new(span, message);
        let text = |data: &[u8]| -> Result<String> {
            std::str::from_utf8(data)
                .map(str::to_owned)
                .map_err(|_| failure("internal error: String contains invalid UTF-8"))
        };
        match op {
            StringOp::Len => {
                let (_, data, _) = self.buffer(&args[0], span)?;
                Ok(Value::Scalar(data.len() as i64))
            }
            StringOp::ScalarLen => {
                let (_, data, _) = self.buffer(&args[0], span)?;
                Ok(Value::Scalar(text(&data)?.chars().count() as i64))
            }
            StringOp::ByteAt => {
                let (_, data, _) = self.buffer(&args[0], span)?;
                let index = usize::try_from(args[1].scalar())
                    .map_err(|_| failure("panic: string byte index out of bounds"))?;
                Ok(Value::Scalar(i64::from(*data.get(index).ok_or_else(
                    || failure("panic: string byte index out of bounds"),
                )?)))
            }
            StringOp::ScalarAt { some_tag, none_tag } => {
                let (_, data, _) = self.buffer(&args[0], span)?;
                let text = text(&data)?;
                let index = args[1].scalar();
                if index < 0 {
                    return Ok(Value::Enum {
                        tag: none_tag,
                        fields: vec![],
                    });
                }
                match text.chars().nth(index as usize) {
                    Some(ch) => Ok(Value::Enum {
                        tag: some_tag,
                        fields: vec![Value::Scalar(i64::from(u32::from(ch)))],
                    }),
                    None => Ok(Value::Enum {
                        tag: none_tag,
                        fields: vec![],
                    }),
                }
            }
            StringOp::FromUtf8 { ok_tag, err_tag } => {
                let Value::Owned(id) = args[0] else {
                    unreachable!("checked owned byte buffer")
                };
                let Some(Value::Buffer { data, capacity }) = self.heap.take(id) else {
                    return Err(failure("internal ownership error: moved byte buffer"));
                };
                let valid = std::str::from_utf8(&data).is_ok();
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(Value::Enum {
                    tag: if valid { ok_tag } else { err_tag },
                    fields: vec![Value::Owned(id)],
                })
            }
            StringOp::AsBytes => {
                let (_, data, _) = self.buffer(&args[0], span)?;
                let data = data.clone();
                let capacity = data.len();
                Ok(self.allocate(Value::Buffer { data, capacity }))
            }
            StringOp::IntoBytes => {
                let Value::Owned(id) = args[0] else {
                    unreachable!("checked owned string")
                };
                Ok(Value::Owned(id))
            }
        }
    }
    /// The validated UTF-8 bytes covered by a borrowed text view. The view
    /// points into its owner's buffer (directly or through a flattened
    /// subview), so this copies only host-side bytes for a read; it performs no
    /// program allocation.
    fn str_data(&self, value: &Value, span: Span) -> Result<Vec<u8>> {
        let Value::Slice {
            base, start, len, ..
        } = value
        else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a &str view",
            ));
        };
        let Value::Borrowed(id) = base.as_ref() else {
            return Err(Diagnostic::new(
                span,
                "internal error: invalid &str view backing storage",
            ));
        };
        let Some(Value::Buffer { data, .. }) = self.heap.get(*id) else {
            return Err(Diagnostic::new(
                span,
                "internal ownership error: dangling text view",
            ));
        };
        let end = start
            .checked_add(*len)
            .ok_or_else(|| Diagnostic::new(span, "internal error: text view range overflowed"))?;
        data.get(*start..end)
            .map(<[u8]>::to_vec)
            .ok_or_else(|| Diagnostic::new(span, "internal error: text view range out of bounds"))
    }
    /// The bytes a new text subview's endpoints are checked against: either a
    /// `String` owner borrow or an existing flattened text view.
    fn text_base_bytes(&self, value: &Value, span: Span) -> Result<Vec<u8>> {
        match value {
            Value::Borrowed(id) => match self.heap.get(*id) {
                Some(Value::Buffer { data, .. }) => Ok(data),
                _ => Err(Diagnostic::new(
                    span,
                    "internal ownership error: dangling text owner",
                )),
            },
            Value::Slice { .. } => self.str_data(value, span),
            _ => Err(Diagnostic::new(
                span,
                "internal error: invalid text view source",
            )),
        }
    }
    fn str_call(&mut self, op: StrOp, args: Vec<Value>, span: Span) -> Result<Value> {
        let data = self.str_data(&args[0], span)?;
        match op {
            StrOp::Len => Ok(Value::Scalar(data.len() as i64)),
            StrOp::ScalarLen => Ok(Value::Scalar(
                data.iter().filter(|byte| (**byte & 0xC0) != 0x80).count() as i64,
            )),
            StrOp::ByteAt => {
                let index = usize::try_from(args[1].scalar())
                    .map_err(|_| Diagnostic::new(span, "panic: text byte index out of bounds"))?;
                Ok(Value::Scalar(i64::from(*data.get(index).ok_or_else(
                    || Diagnostic::new(span, "panic: text byte index out of bounds"),
                )?)))
            }
            StrOp::ScalarAt { some_tag, none_tag } => {
                let index = args[1].scalar();
                if index < 0 {
                    return Ok(Value::Enum {
                        tag: none_tag,
                        fields: vec![],
                    });
                }
                let text = std::str::from_utf8(&data)
                    .map_err(|_| Diagnostic::new(span, "internal error: invalid text view"))?;
                match text.chars().nth(index as usize) {
                    Some(ch) => Ok(Value::Enum {
                        tag: some_tag,
                        fields: vec![Value::Scalar(i64::from(u32::from(ch)))],
                    }),
                    None => Ok(Value::Enum {
                        tag: none_tag,
                        fields: vec![],
                    }),
                }
            }
            StrOp::ToString => {
                let capacity = data.len();
                Ok(self.allocate(Value::Buffer { data, capacity }))
            }
        }
    }
    fn slice_len(&self, value: &Value, span: Span) -> Result<usize> {
        match value {
            Value::Slice { len, .. } => Ok(*len),
            Value::Enum { fields, .. } => Ok(fields.len()),
            Value::Borrowed(id) => match self.heap.get(*id) {
                Some(Value::Buffer { data, .. }) => Ok(data.len()),
                Some(Value::Vector { items, .. }) => Ok(items.len()),
                _ => Err(Diagnostic::new(
                    span,
                    "internal ownership error: dangling slice source",
                )),
            },
            _ => Err(Diagnostic::new(
                span,
                "internal error: invalid slice source",
            )),
        }
    }
    fn slice_element(&self, view: &Value, index: usize, span: Span) -> Result<Value> {
        let Value::Slice {
            base,
            start,
            len,
            array,
        } = view
        else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a slice view",
            ));
        };
        if index >= *len {
            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
        }
        let position = start + index;
        if let Some(cell) = array {
            let value = cell.lock().unwrap();
            return match &*value {
                Value::Enum { fields, .. } => fields.get(position).cloned().ok_or_else(|| {
                    Diagnostic::new(span, "internal error: slice array index out of bounds")
                }),
                _ => Err(Diagnostic::new(
                    span,
                    "internal error: invalid array slice source",
                )),
            };
        }
        match base.as_ref() {
            Value::Enum { fields, .. } => fields.get(position).cloned().ok_or_else(|| {
                Diagnostic::new(span, "internal error: slice array index out of bounds")
            }),
            Value::Borrowed(id) => match self.heap.get(*id) {
                Some(Value::Buffer { data, .. }) => data
                    .get(position)
                    .map(|byte| Value::Scalar(i64::from(*byte)))
                    .ok_or_else(|| Diagnostic::new(span, "panic: slice index out of bounds")),
                Some(Value::Vector { items, .. }) => items
                    .get(position)
                    .cloned()
                    .ok_or_else(|| Diagnostic::new(span, "panic: slice index out of bounds")),
                _ => Err(Diagnostic::new(
                    span,
                    "internal ownership error: dangling slice source",
                )),
            },
            _ => Err(Diagnostic::new(
                span,
                "internal error: invalid slice source",
            )),
        }
    }
    fn slice_set(&mut self, view: &Value, index: usize, value: Value, span: Span) -> Result<()> {
        let Value::Slice {
            base,
            start,
            len,
            array,
        } = view
        else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a slice view",
            ));
        };
        if index >= *len {
            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
        }
        let position = start + index;
        if let Some(cell) = array {
            let mut cell = cell.lock().unwrap();
            return match &mut *cell {
                Value::Enum { fields, .. } => {
                    let Some(slot) = fields.get_mut(position) else {
                        return Err(Diagnostic::new(
                            span,
                            "internal error: slice array index out of bounds",
                        ));
                    };
                    *slot = value;
                    Ok(())
                }
                _ => Err(Diagnostic::new(
                    span,
                    "internal error: invalid array slice source",
                )),
            };
        }
        match base.as_ref() {
            Value::Borrowed(id) => {
                let Some(mut current) = self.heap.get(*id) else {
                    return Err(Diagnostic::new(
                        span,
                        "internal ownership error: dangling slice source",
                    ));
                };
                match &mut current {
                    Value::Buffer { data, .. } => {
                        let byte = u8::try_from(value.scalar())
                            .map_err(|_| Diagnostic::new(span, "panic: byte value out of range"))?;
                        let Some(slot) = data.get_mut(position) else {
                            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
                        };
                        *slot = byte;
                    }
                    Value::Vector { items, .. } => {
                        let Some(slot) = items.get_mut(position) else {
                            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
                        };
                        *slot = value;
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            span,
                            "internal ownership error: dangling slice source",
                        ));
                    }
                }
                self.heap.insert(*id, current);
                Ok(())
            }
            _ => Err(Diagnostic::new(
                span,
                "internal error: invalid slice source for a mutable view",
            )),
        }
    }
    fn slice_call(&mut self, op: SliceOp, args: Vec<Value>, span: Span) -> Result<Value> {
        match op {
            SliceOp::Len => {
                let len = self.slice_len(&args[0], span)?;
                Ok(Value::Scalar(len as i64))
            }
            SliceOp::TryGet {
                some_tag,
                none_tag,
                option: _,
            } => {
                let len = self.slice_len(&args[0], span)?;
                let Some(index) = usize::try_from(args[1].scalar())
                    .ok()
                    .filter(|index| *index < len)
                else {
                    return Ok(Value::Enum {
                        tag: none_tag,
                        fields: vec![],
                    });
                };
                let element = self.slice_element(&args[0], index, span)?;
                Ok(Value::Enum {
                    tag: some_tag,
                    fields: vec![element],
                })
            }
            SliceOp::Get | SliceOp::At => {
                let index = usize::try_from(args[1].scalar())
                    .map_err(|_| Diagnostic::new(span, "panic: slice index out of bounds"))?;
                if op == SliceOp::Get && index >= self.slice_len(&args[0], span)? {
                    return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
                }
                self.slice_element(&args[0], index, span)
            }
            SliceOp::Set => {
                let index = usize::try_from(args[1].scalar())
                    .map_err(|_| Diagnostic::new(span, "panic: slice index out of bounds"))?;
                if index >= self.slice_len(&args[0], span)? {
                    return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
                }
                self.slice_set(&args[0], index, args[2].clone(), span)?;
                Ok(Value::Scalar(0))
            }
        }
    }
    fn vec_call(&mut self, op: VecOp, args: Vec<Value>, span: Span) -> Result<Value> {
        const LIMIT: usize = 1 << 20;
        let failure = |message: &str| Diagnostic::new(span, message.to_owned());
        let index_of = |value: &Value, len: usize| {
            usize::try_from(value.scalar())
                .ok()
                .filter(|i| *i < len)
                .ok_or_else(|| failure("panic: vector index out of bounds"))
        };
        match op {
            VecOp::WithCapacity => {
                let capacity = usize::try_from(args[0].scalar())
                    .map_err(|_| failure("panic: negative vector capacity"))?;
                if capacity > LIMIT {
                    return Err(failure(
                        "reference vector capacity budget exhausted (1Mi elements)",
                    ));
                }
                Ok(self.allocate(Value::Vector {
                    items: Vec::new(),
                    capacity,
                }))
            }
            VecOp::Clear => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Vector {
                    mut items,
                    capacity,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                // Dropping from the end releases elements in reverse order
                // exactly once. The allocation and its capacity are retained.
                while let Some(item) = items.pop() {
                    self.drop_value(item)?;
                }
                self.heap.insert(id, Value::Vector { items, capacity });
                Ok(Value::Owned(id))
            }
            VecOp::Reserve => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let additional = usize::try_from(args[1].scalar())
                    .map_err(|_| failure("panic: negative vector reserve"))?;
                let Some(Value::Vector { items, capacity }) = self.heap.take(id) else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                let needed = items
                    .len()
                    .checked_add(additional)
                    .ok_or_else(|| failure("panic: vector reserve length overflow"))?;
                if needed > LIMIT {
                    return Err(failure(
                        "reference vector capacity budget exhausted (1Mi elements)",
                    ));
                }
                let mut capacity = capacity;
                // Reserve grows once to exactly the requested length. It does
                // not speculate capacity beyond `len + additional`.
                if needed > capacity {
                    capacity = needed;
                    self.stats.growth();
                }
                self.heap.insert(id, Value::Vector { items, capacity });
                Ok(Value::Owned(id))
            }
            VecOp::Len | VecOp::Get | VecOp::At => {
                let Value::Borrowed(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Vector { items, .. }) = self.heap.get(id) else {
                    return Err(failure("internal ownership error: dangling vector"));
                };
                match op {
                    VecOp::Len => Ok(Value::Scalar(items.len() as i64)),
                    VecOp::Get => Ok(items[index_of(&args[1], items.len())?].clone()),
                    _ => items
                        .get(usize::try_from(args[1].scalar()).unwrap_or(usize::MAX))
                        .cloned()
                        .ok_or_else(|| {
                            failure("internal error: proved vector index out of bounds")
                        }),
                }
            }
            VecOp::Push | VecOp::Set => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let mut args = args.into_iter().skip(1);
                let (index, value) = if op == VecOp::Set {
                    (Some(args.next().unwrap()), args.next().unwrap())
                } else {
                    (None, args.next().unwrap())
                };
                let Some(Value::Vector {
                    mut items,
                    mut capacity,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                if let Some(index) = index {
                    let index = index_of(&index, items.len())?;
                    let old = std::mem::replace(&mut items[index], value);
                    self.heap.insert(id, Value::Vector { items, capacity });
                    self.drop_value(old)?;
                    return Ok(Value::Owned(id));
                }
                if items.len() == capacity {
                    let next = if capacity == 0 {
                        4
                    } else {
                        capacity.saturating_mul(2)
                    };
                    if next > LIMIT {
                        return Err(failure(
                            "reference vector capacity budget exhausted (1Mi elements)",
                        ));
                    }
                    capacity = next;
                    self.stats.growth();
                }
                items.push(value);
                self.heap.insert(id, Value::Vector { items, capacity });
                Ok(Value::Owned(id))
            }
        }
    }
    /// Apply one or more checked callback steps in place. The vector's host
    /// item buffer and capacity are preserved; no storage is acquired.
    fn vec_map_call(&mut self, id: usize, functions: Vec<Value>, span: Span) -> Result<Value> {
        // Keep the live vector allocation represented while callbacks execute;
        // removing it would undercount peak-live when a callback allocates.
        let Some(Value::Vector {
            mut items,
            capacity,
        }) = self.heap.take(id)
        else {
            return Err(Diagnostic::new(
                span,
                "internal ownership error: moved vector in map_in_place",
            ));
        };
        for item in items.iter_mut() {
            let mut current = std::mem::replace(item, Value::Scalar(0));
            for function in &functions {
                let Value::Function {
                    function,
                    environment: None,
                } = function
                else {
                    return Err(Diagnostic::new(
                        span,
                        "internal ownership error: map_in_place received a once closure",
                    ));
                };
                current = self.call(*function, vec![current])?;
            }
            *item = current;
        }
        self.heap.insert(id, Value::Vector { items, capacity });
        Ok(Value::Owned(id))
    }
    fn io_call(
        &mut self,
        op: IoOp,
        shape: Option<ResultShape>,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value> {
        match op {
            IoOp::Stdin => return Ok(Value::Scalar(0)),
            IoOp::Stdout => return Ok(Value::Scalar(1)),
            _ => {}
        }
        let shape = shape.expect("checked I/O result shape");
        let (status, value) = match op {
            IoOp::ReadAll | IoOp::ReadLine | IoOp::ReadChunk => {
                let Value::Owned(id) = args[1] else {
                    unreachable!()
                };
                let Some(Value::Buffer { mut data, capacity }) = self.heap.take(id) else {
                    unreachable!()
                };
                let mut length = data.len();
                // Storage was reserved by the constructor. No buffer growth occurs here.
                data.resize(capacity, 0);
                let mut probe = [0u8; 1];
                let status = loop {
                    self.fuel = self.fuel.checked_sub(1).ok_or_else(|| {
                        Diagnostic::new(span, "reference I/O computation budget exhausted")
                    })?;
                    let full = length == capacity;
                    let line = matches!(op, IoOp::ReadLine);
                    let chunk = matches!(op, IoOp::ReadChunk);
                    if full && chunk {
                        break 27;
                    }
                    let target = if full {
                        &mut probe[..]
                    } else {
                        &mut data[length..if line { length + 1 } else { capacity }]
                    };
                    match self.input.read(target) {
                        Ok(0) => break 0,
                        Ok(_) if full => break 27, // Linux EFBIG: bounded input exceeded capacity.
                        Ok(count) => {
                            length += count;
                            if chunk || (line && data[length - 1] == b'\n') {
                                break 0;
                            }
                        }
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(error) => break io_error_code(&error),
                    }
                };
                data.truncate(length);
                if status != 0 {
                    // The consumed buffer is destroyed on failure.
                    self.stats.deallocation();
                } else {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                }
                (status, Value::Owned(id))
            }
            IoOp::Write => {
                // Read-only access to storage and mutable access to the output are disjoint.
                let Value::Borrowed(id) = args[1] else {
                    unreachable!()
                };
                let Some(Value::Buffer { data, .. }) = self.heap.get(id) else {
                    unreachable!()
                };
                let length = data.len();
                let mut offset = 0;
                let status = loop {
                    if offset == length {
                        break 0;
                    }
                    self.fuel = self.fuel.checked_sub(1).ok_or_else(|| {
                        Diagnostic::new(span, "reference I/O computation budget exhausted")
                    })?;
                    match self.output.write(&data[offset..]) {
                        Ok(0) => break 5, // Linux EIO, including an unsuccessful zero-length write.
                        Ok(count) => offset += count,
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(error) => break io_error_code(&error),
                    }
                };
                (status, Value::Scalar(0))
            }
            _ => unreachable!(),
        };
        Ok(Value::Enum {
            tag: if status == 0 {
                shape.ok_tag
            } else {
                shape.err_tag
            },
            fields: vec![if status == 0 {
                value
            } else {
                Value::Scalar(status)
            }],
        })
    }
    fn consume(&self, expr: &Expr, frame: &mut Frame) {
        if let Some(id) = expr.resource {
            frame.resources[id] = None;
        }
    }
    fn local_active(&self, slot: usize, frame: &mut Frame) {
        if let Some(id) = self.program.functions[frame.function].local_resources[slot] {
            frame.resources[id] = Some(self.materialize(frame.locals[slot].clone()));
        }
    }
    fn drop_value(&mut self, value: Value) -> Result<()> {
        match value {
            Value::Owned(id) => {
                let value = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal ownership error: double free")
                })?;
                self.stats.deallocation();
                self.drop_value(value)?;
            }
            Value::Enum { fields, .. } => {
                for field in fields.into_iter().rev() {
                    self.drop_value(field)?;
                }
            }
            Value::Union { value, .. } => self.drop_value(*value)?,
            Value::Function {
                environment: Some(id),
                ..
            } => {
                let value = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(
                        Span::default(),
                        "internal ownership error: double closure drop",
                    )
                })?;
                self.stats.deallocation();
                self.drop_value(value)?;
            }
            Value::Closure { captures } => {
                for capture in captures.into_iter().rev() {
                    self.drop_value(capture)?;
                }
            }
            Value::Vector { items, .. } => {
                for item in items.into_iter().rev() {
                    self.drop_value(item)?;
                }
            }
            Value::Arena { state } => self.arena_release(&state)?,
            Value::ArenaBox { state, slot } => {
                let payload = state
                    .lock()
                    .unwrap()
                    .slots
                    .get_mut(slot)
                    .and_then(|slot| slot.take());
                if let Some(payload) = payload {
                    self.drop_value(payload)?;
                }
                self.arena_release(&state)?;
            }
            // A slice view borrows its base and owns nothing.
            Value::Slice { .. } => {}
            _ => {}
        }
        Ok(())
    }
    fn drop_resource(&mut self, id: Option<usize>, frame: &mut Frame) -> Result<()> {
        if let Some(id) = id
            && let Some(value) = frame.resources[id].take()
        {
            self.drop_value(value)?;
        }
        Ok(())
    }
    fn cleanup(&mut self, frame: &mut Frame) -> Result<()> {
        for id in (0..frame.resources.len()).rev() {
            self.drop_resource(Some(id), frame)?;
        }
        Ok(())
    }
    fn task_comm(&mut self) -> Result<&mut TaskComm> {
        self.task.as_mut().ok_or_else(|| {
            Diagnostic::new(
                Span::default(),
                "internal error: task operation outside a scheduled task",
            )
        })
    }
    fn call_value(&mut self, callable: Value, arguments: Vec<Value>) -> Result<Value> {
        let Value::Function {
            function,
            environment,
        } = callable
        else {
            return Err(Diagnostic::new(
                Span::default(),
                "internal error: task body is not callable",
            ));
        };
        match environment {
            None => self.call(function, arguments),
            Some(environment) => {
                let Some(Value::Closure { captures }) = self.heap.take(environment) else {
                    return Err(Diagnostic::new(
                        Span::default(),
                        "internal ownership error: dangling task closure environment",
                    ));
                };
                self.stats.deallocation();
                self.call_with(function, captures, arguments)
            }
        }
    }
    fn task_scope_end(&mut self) -> Result<()> {
        let children = self.task_comm()?.scope_children()?;
        let mut failure = None;
        for child in children {
            match self.task_comm()?.join(child)? {
                TaskOutcome::Completed(value, preserve) => {
                    if preserve {
                        return Err(Diagnostic::new(
                            Span::default(),
                            "internal error: an unjoined task result carrying a linear obligation reached the scope epilogue; join it explicitly before the scope ends",
                        ));
                    }
                    self.drop_value(value)?
                }
                TaskOutcome::Cancelled => {}
                TaskOutcome::Failed(error) => {
                    if failure.is_none() {
                        failure = Some(error);
                    }
                }
            }
        }
        match failure {
            Some(error) => Err(error),
            None => Ok(()),
        }
    }
    fn call(&mut self, index: usize, args: Vec<Value>) -> Result<Value> {
        self.call_with(index, vec![], args)
    }
    fn call_with(&mut self, index: usize, captures: Vec<Value>, args: Vec<Value>) -> Result<Value> {
        let f = &self.program.functions[index];
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                f.span,
                "reference evaluator call-depth budget exhausted",
            ));
        }
        self.depth += 1;
        let mut frame = Frame {
            function: index,
            locals: vec![Value::Scalar(0); f.locals.len()],
            resources: vec![None; f.resources.len()],
        };
        let initial = captures.len() + args.len();
        frame.locals[..initial]
            .clone_from_slice(&captures.into_iter().chain(args).collect::<Vec<_>>());
        for slot in 0..initial {
            self.local_active(slot, &mut frame);
        }
        let result = self.block(&f.body, &mut frame);
        self.depth -= 1;
        let flow = result?;
        self.cleanup(&mut frame)?;
        Ok(match flow {
            Flow::Value(v) | Flow::Return(v) => v,
            Flow::Break(_) | Flow::Continue => unreachable!("loop exits are checked"),
        })
    }
    fn block(&mut self, block: &Block, frame: &mut Frame) -> Result<Flow> {
        let mut slots = Vec::new();
        for statement in &block.statements {
            match statement {
                Statement::Let(slot, expr) => {
                    let value = value!(self.expr(expr, frame));
                    self.consume(expr, frame);
                    if self.erased_local(*slot, frame) {
                        continue;
                    }
                    self.store_local(*slot, value, frame);
                    self.local_active(*slot, frame);
                    slots.push(*slot);
                }
                Statement::Expr(expr) => {
                    value!(self.expr(expr, frame));
                    self.drop_resource(expr.resource, frame)?;
                }
            }
        }
        let value = if let Some(tail) = &block.tail {
            let value = value!(self.expr(tail, frame));
            self.consume(tail, frame);
            value
        } else {
            Value::Scalar(0)
        };
        for slot in slots.into_iter().rev() {
            self.drop_resource(
                self.program.functions[frame.function].local_resources[slot],
                frame,
            )?;
        }
        Ok(Flow::Value(value))
    }
    fn expr(&mut self, expr: &Expr, frame: &mut Frame) -> Result<Flow> {
        if self.depth >= 128 {
            return Err(Diagnostic::new(
                expr.span,
                "reference evaluator nesting budget exhausted",
            ));
        }
        self.depth += 1;
        let result = self.expression(expr, frame);
        self.depth -= 1;
        if let Ok(Flow::Value(value)) = &result
            && let Some(id) = expr.resource
        {
            frame.resources[id] = Some(value.clone());
        }
        result
    }
    fn expression(&mut self, expr: &Expr, frame: &mut Frame) -> Result<Flow> {
        if self.fuel == 0 {
            return Err(Diagnostic::new(
                expr.span,
                "reference evaluator computation budget exhausted",
            ));
        }
        self.fuel -= 1;
        let panic = || Diagnostic::new(expr.span, "panic: checked arithmetic failed");
        let result = match &expr.kind {
            ExprKind::Constant(n) => Value::Scalar(*n),
            ExprKind::FnValue { function, captures } => {
                if captures.is_empty() {
                    Value::Function {
                        function: *function,
                        environment: None,
                    }
                } else {
                    let mut values = Vec::with_capacity(captures.len());
                    for capture in captures {
                        values.push(value!(self.expr(capture, frame)));
                    }
                    for capture in captures {
                        self.consume(capture, frame);
                    }
                    let environment = self.allocate(Value::Closure { captures: values });
                    let Value::Owned(environment) = environment else {
                        unreachable!()
                    };
                    Value::Function {
                        function: *function,
                        environment: Some(environment),
                    }
                }
            }
            ExprKind::CallIndirect { callee, arguments } => {
                let callable = value!(self.expr(callee, frame));
                let mut values = Vec::with_capacity(arguments.len());
                for argument in arguments {
                    values.push(value!(self.expr(argument, frame)));
                }
                self.consume(callee, frame);
                for argument in arguments {
                    self.consume(argument, frame);
                }
                let Value::Function {
                    function,
                    environment,
                } = callable
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: indirect call received a non-callable value",
                    ));
                };
                match environment {
                    None => self.call(function, values)?,
                    Some(environment) => {
                        let Some(Value::Closure { captures }) = self.heap.take(environment) else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: dangling closure environment",
                            ));
                        };
                        self.stats.deallocation();
                        self.call_with(function, captures, values)?
                    }
                }
            }
            ExprKind::TaskSpawn {
                body, obligation, ..
            } => {
                let callable = value!(self.expr(body, frame));
                let Value::Function {
                    function,
                    environment,
                } = callable
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: Task.spawn body is not callable",
                    ));
                };
                self.consume(body, frame);
                let id = self
                    .task_comm()?
                    .spawn(function, environment, *obligation)?;
                Value::Task(id)
            }
            ExprKind::TaskScope { body, failure, .. } => {
                let callable = value!(self.expr(body, frame));
                self.consume(body, frame);
                self.task_comm()?.scope_begin()?;
                let result = self.call_value(callable, vec![]);
                if let (Ok(Value::Enum { tag, .. }), Some(shape)) = (&result, *failure)
                    && *tag == shape.err_tag
                {
                    self.task_comm()?.cancel_scope()?;
                }
                let end = self.task_scope_end();
                match (result, end) {
                    (Ok(value), Ok(())) => value,
                    (Err(error), _) => return Err(error),
                    (Ok(value), Err(error)) => {
                        self.drop_value(value)?;
                        return Err(error);
                    }
                }
            }
            ExprKind::TaskYield => {
                let cancelled = self.task_comm()?.yield_now()?;
                Value::Scalar(i64::from(cancelled))
            }
            ExprKind::TaskCheckCancel => {
                let cancelled = self.task_comm()?.check_cancel();
                Value::Scalar(i64::from(cancelled))
            }
            ExprKind::TaskCancel(reference) => {
                let reference = value!(self.expr(reference, frame));
                let Value::TaskRef(id) = reference else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: Task.cancel received a non-task borrow",
                    ));
                };
                self.task_comm()?.cancel(id)?;
                Value::Scalar(0)
            }
            ExprKind::TaskJoin { task, exit, .. } => {
                let handle = value!(self.expr(task, frame));
                self.consume(task, frame);
                let Value::Task(id) = handle else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: Task.join received a non-task handle",
                    ));
                };
                match self.task_comm()?.join(id)? {
                    TaskOutcome::Completed(value, _) => Value::Enum {
                        tag: exit.completed_tag,
                        fields: vec![value],
                    },
                    TaskOutcome::Cancelled => Value::Enum {
                        tag: exit.cancelled_tag,
                        fields: vec![Value::Scalar(0); self.program.width(exit.payload)],
                    },
                    TaskOutcome::Failed(error) => return Err(error),
                }
            }

            ExprKind::BytesLiteral(bytes) => self.allocate(Value::Buffer {
                data: bytes.clone(),
                capacity: bytes.len(),
            }),
            ExprKind::Coerce {
                value,
                to,
                coercion,
            } => {
                let _ = to;
                let inner = value!(self.expr(value, frame));
                self.consume(value, frame);
                match coercion {
                    Coercion::Inject { tag } => Value::Union {
                        tag: *tag,
                        value: Box::new(inner),
                    },
                    Coercion::Repack { map } => {
                        let Value::Union { tag, value } = inner else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: union repacking received a non-union value",
                            ));
                        };
                        let Some(tag) = map.get(tag).copied() else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: union repacking has no alternative mapping",
                            ));
                        };
                        Value::Union { tag, value }
                    }
                }
            }
            ExprKind::Local(slot) | ExprKind::Peek(slot) => {
                self.materialize(frame.locals[*slot].clone())
            }
            ExprKind::Project(base, offset) => {
                let value = value!(self.expr(base, frame));
                let (ty, value) = match value {
                    Value::RecordRef(cell) => {
                        let pointer = base.ty.ref_pointee().expect("record reference");
                        (self.program.pointees[pointer], cell.lock().unwrap().clone())
                    }
                    value => (base.ty, value),
                };
                project(
                    &self.program.enums,
                    &self.program.unions,
                    &self.program.function_types,
                    ty,
                    value,
                    *offset,
                )
            }
            ExprKind::Slice {
                base,
                start,
                end,
                element: _,
                check,
                split: _,
                text,
            } => {
                let array = match &base.kind {
                    ExprKind::Peek(slot) | ExprKind::Local(slot)
                        if self.program.functions[frame.function].locals[*slot]
                            .ty
                            .layout()
                            .is_some_and(|id| self.program.enums[id].array.is_some()) =>
                    {
                        let current = frame.locals[*slot].clone();
                        let cell = match current {
                            Value::ArrayCell(cell) => cell,
                            value => {
                                let cell = Arc::new(Mutex::new(value));
                                frame.locals[*slot] = Value::ArrayCell(cell.clone());
                                cell
                            }
                        };
                        Some(cell)
                    }
                    _ => None,
                };
                let base_value = match &array {
                    Some(cell) => cell.lock().unwrap().clone(),
                    None => value!(self.expr(base, frame)),
                };
                let base_len = self.slice_len(&base_value, expr.span)?;
                let start = match start {
                    Some(start) => value!(self.expr(start, frame)).scalar(),
                    None => 0,
                };
                let end = match end {
                    Some(end) => value!(self.expr(end, frame)).scalar(),
                    None => base_len as i64,
                };
                let (start, end) = (usize::try_from(start).ok(), usize::try_from(end).ok());
                let (Some(start), Some(end)) = (start, end) else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "panic: slice range out of bounds",
                    ));
                };
                if *check && (start > end || end > base_len) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "panic: slice range out of bounds",
                    ));
                }
                if *text && *check {
                    let bytes = self.text_base_bytes(&base_value, expr.span)?;
                    let boundary =
                        |index: usize| index == bytes.len() || bytes[index] & 0xC0 != 0x80;
                    if !boundary(start) || !boundary(end) {
                        return Err(Diagnostic::new(
                            expr.span,
                            "panic: text range is not on Unicode scalar boundaries",
                        ));
                    }
                }
                match base_value {
                    Value::Slice {
                        base,
                        start: prior,
                        len: _,
                        array: prior_array,
                    } => Value::Slice {
                        base,
                        start: prior + start,
                        len: end - start,
                        array: array.or(prior_array),
                    },
                    base => Value::Slice {
                        base: Box::new(base),
                        start,
                        len: end - start,
                        array,
                    },
                }
            }
            ExprKind::BytesAt(bytes, index) => {
                let reference = value!(self.expr(bytes, frame));
                let index = value!(self.expr(index, frame)).scalar();
                let (_, data, _) = self.buffer(&reference, expr.span)?;
                // The bound was proved statically; a failure here is a compiler bug.
                let byte = data
                    .get(usize::try_from(index).unwrap_or(usize::MAX))
                    .ok_or_else(|| {
                        Diagnostic::new(
                            expr.span,
                            "internal error: proved byte index out of bounds",
                        )
                    })?;
                Value::Scalar(i64::from(*byte))
            }
            ExprKind::While(condition, body) => loop {
                let test = value!(self.expr(condition, frame)).scalar();
                if test == 0 {
                    break Value::Scalar(0);
                }
                match self.block(body, frame)? {
                    Flow::Value(_) | Flow::Continue => {}
                    Flow::Break(_) => break Value::Scalar(0),
                    returned @ Flow::Return(_) => return Ok(returned),
                }
            },
            ExprKind::Loop(body) => loop {
                self.fuel = self.fuel.checked_sub(1).ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "reference evaluator computation budget exhausted",
                    )
                })?;
                match self.block(body, frame)? {
                    Flow::Value(_) | Flow::Continue => {}
                    Flow::Break(value) => break value,
                    returned @ Flow::Return(_) => return Ok(returned),
                }
            },
            ExprKind::Break(value, cleanup) => {
                let value = match value {
                    Some(value) => {
                        let v = value!(self.expr(value, frame));
                        self.consume(value, frame);
                        v
                    }
                    None => Value::Scalar(0),
                };
                for id in cleanup {
                    self.drop_resource(Some(*id), frame)?;
                }
                return Ok(Flow::Break(value));
            }
            ExprKind::Continue(cleanup) => {
                for id in cleanup {
                    self.drop_resource(Some(*id), frame)?;
                }
                return Ok(Flow::Continue);
            }
            ExprKind::Move(slot) => {
                if let Some(id) = self.program.functions[frame.function].local_resources[*slot] {
                    frame.resources[id] = None;
                }
                self.materialize(frame.locals[*slot].clone())
            }
            ExprKind::Borrow(slot) => {
                let ty = self.program.functions[frame.function].locals[*slot].ty;
                if ty.layout().is_some_and(|id| self.program.enums[id].record) {
                    let current = frame.locals[*slot].clone();
                    let cell = match current {
                        Value::RecordCell(cell) => cell,
                        value => {
                            let cell = Arc::new(Mutex::new(value));
                            frame.locals[*slot] = Value::RecordCell(cell.clone());
                            cell
                        }
                    };
                    Value::RecordRef(cell)
                } else {
                    match frame.locals[*slot].clone() {
                        Value::Owned(id) => Value::Borrowed(id),
                        Value::Task(id) => Value::TaskRef(id),
                        Value::Arena { state } => Value::ArenaRef(state),
                        Value::ArenaBox { state, slot } => Value::ArenaBoxRef { state, slot },
                        _ => unreachable!("checked borrow of an owned handle"),
                    }
                }
            }
            ExprKind::BoxNew(arg) => {
                let value = value!(self.expr(arg, frame));
                self.consume(arg, frame);
                self.allocate(value)
            }
            ExprKind::BoxTake(arg) => {
                let Value::Owned(id) = value!(self.expr(arg, frame)) else {
                    unreachable!()
                };
                self.consume(arg, frame);
                let value = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal ownership error: stale box")
                })?;
                self.stats.deallocation();
                value
            }
            ExprKind::BoxRead(arg) => {
                let Value::Borrowed(id) = value!(self.expr(arg, frame)) else {
                    unreachable!()
                };
                self.heap.get(id).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal ownership error: dangling borrow")
                })?
            }
            ExprKind::BoxReuse { owner, payload } => {
                let Value::Owned(id) = value!(self.expr(owner, frame)) else {
                    unreachable!("checked Box.reuse owner")
                };
                let new = value!(self.expr(payload, frame));
                // Both arguments have been evaluated. Only now is the old
                // affine payload destroyed. The outer allocation is preserved.
                self.consume(owner, frame);
                self.consume(payload, frame);
                let old = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal ownership error: stale reuse box")
                })?;
                self.drop_value(old)?;
                self.heap.insert(id, new);
                self.stats.reuse();
                Value::Owned(id)
            }
            ExprKind::BoxReuseGrow { owner, payload } => {
                let Value::Owned(id) = value!(self.expr(owner, frame)) else {
                    unreachable!("checked Box.reuse_grow owner")
                };
                let new = value!(self.expr(payload, frame));
                // Both arguments are evaluated before the old payload is
                // destroyed. The reference model always has logical room, so
                // growth never moves the reference allocation id.
                self.consume(owner, frame);
                self.consume(payload, frame);
                let old = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal ownership error: stale reuse box")
                })?;
                self.drop_value(old)?;
                self.heap.insert(id, new);
                self.stats.reuse();
                Value::Owned(id)
            }
            ExprKind::ArenaNew => self.arena_new_value(),
            ExprKind::ArenaAlloc { arena, value } => {
                let Value::ArenaRef(state) = value!(self.expr(arena, frame)) else {
                    unreachable!("checked arena borrow")
                };
                let payload = value!(self.expr(value, frame));
                self.consume(arena, frame);
                self.consume(value, frame);
                self.arena_allocate(&state, payload)
            }
            ExprKind::ArenaBoxRead(argument) => {
                let Value::ArenaBoxRef { state, slot } = value!(self.expr(argument, frame)) else {
                    unreachable!("checked arena box borrow")
                };
                state
                    .lock()
                    .unwrap()
                    .slots
                    .get(slot)
                    .and_then(|slot| slot.clone())
                    .ok_or_else(|| {
                        Diagnostic::new(expr.span, "internal ownership error: stale arena box")
                    })?
            }
            ExprKind::ArenaBoxTake(argument) => {
                let Value::ArenaBox { state, slot } = value!(self.expr(argument, frame)) else {
                    unreachable!("checked arena box take")
                };
                self.consume(argument, frame);
                let payload = state
                    .lock()
                    .unwrap()
                    .slots
                    .get_mut(slot)
                    .and_then(|slot| slot.take())
                    .ok_or_else(|| {
                        Diagnostic::new(expr.span, "internal ownership error: stale arena box")
                    })?;
                self.arena_release(&state)?;
                payload
            }
            ExprKind::BoxTryNew {
                value: argument,
                shape,
            } => {
                let value = value!(self.expr(argument, frame));
                self.consume(argument, frame);
                if self.try_charge() {
                    let owner = self.allocate(value);
                    Value::Enum {
                        tag: shape.ok_tag,
                        fields: vec![owner],
                    }
                } else {
                    Value::Enum {
                        tag: shape.err_tag,
                        fields: vec![value],
                    }
                }
            }
            ExprKind::BoxTryReuse {
                owner,
                payload,
                shape,
            } => {
                let Value::Owned(id) = value!(self.expr(owner, frame)) else {
                    unreachable!("checked Box.try_reuse owner")
                };
                let new = value!(self.expr(payload, frame));
                self.consume(owner, frame);
                self.consume(payload, frame);
                let Type::Box(old_index) = owner.ty else {
                    unreachable!("checked Box.try_reuse owner type")
                };
                let old_width = self.program.width(self.program.pointees[old_index]);
                let new_width = self.program.width(payload.ty);
                // A non-widening reuse needs no allocator action and therefore
                // cannot fail. Only a growth attempt consumes the probe budget.
                if new_width <= old_width || self.try_charge() {
                    let previous = self.heap.take(id).ok_or_else(|| {
                        Diagnostic::new(expr.span, "internal ownership error: stale reuse box")
                    })?;
                    self.drop_value(previous)?;
                    self.heap.insert(id, new);
                    self.stats.reuse();
                    Value::Enum {
                        tag: shape.ok_tag,
                        fields: vec![Value::Owned(id)],
                    }
                } else {
                    // The payload is checked non-owning, so discarding it
                    // loses no supplied owner; the original owner is intact.
                    self.drop_value(new)?;
                    Value::Enum {
                        tag: shape.err_tag,
                        fields: vec![Value::Owned(id)],
                    }
                }
            }
            ExprKind::BytesTryWithCapacity { capacity, shape } => {
                const LIMIT: usize = 16 * 1024 * 1024;
                let requested = value!(self.expr(capacity, frame)).scalar();
                self.consume(capacity, frame);
                let attempt = usize::try_from(requested)
                    .ok()
                    .filter(|capacity| *capacity <= LIMIT && self.try_charge())
                    .and_then(|capacity| {
                        let mut data = Vec::new();
                        data.try_reserve_exact(capacity).ok()?;
                        Some((capacity, data))
                    });
                match attempt {
                    Some((capacity, data)) => {
                        let buffer = self.allocate(Value::Buffer { data, capacity });
                        Value::Enum {
                            tag: shape.ok_tag,
                            fields: vec![buffer],
                        }
                    }
                    None => Value::Enum {
                        tag: shape.err_tag,
                        fields: vec![Value::Scalar(requested)],
                    },
                }
            }
            ExprKind::Drop(arg) => {
                let value = value!(self.expr(arg, frame));
                self.consume(arg, frame);
                self.drop_value(value)?;
                Value::Scalar(0)
            }
            ExprKind::Block(b) => return self.block(b, frame),
            ExprKind::Construct { tag, fields, .. } => {
                let mut values = Vec::new();
                for field in fields {
                    values.push(value!(self.expr(field, frame)));
                }
                for field in fields {
                    self.consume(field, frame);
                }
                Value::Enum {
                    tag: *tag,
                    fields: values,
                }
            }
            ExprKind::Try {
                value,
                input,
                output,
            } => {
                let Value::Enum { tag, mut fields } = value!(self.expr(value, frame)) else {
                    unreachable!()
                };
                self.consume(value, frame);
                if tag == input.ok_tag {
                    fields.remove(0)
                } else {
                    self.cleanup(frame)?;
                    return Ok(Flow::Return(Value::Enum {
                        tag: output.err_tag,
                        fields,
                    }));
                }
            }
            ExprKind::Unary(op, operand) => {
                let n = value!(self.expr(operand, frame)).scalar();
                let float_kind = operand.ty.float_kind();
                if let Some(kind) = float_kind {
                    debug_assert_eq!(*op, Kind::Minus);
                    return Ok(Flow::Value(Value::Scalar(crate::float::negate(kind, n))));
                }
                let kind = operand.ty.int_kind();
                Value::Scalar(match (op, kind) {
                    (Kind::Minus, Some(kind)) => kind.encode(-kind.decode(n)).ok_or_else(panic)?,
                    (Kind::Minus, None) => n.checked_neg().ok_or_else(panic)?,
                    (Kind::Bang, Some(kind)) => crate::int::not(kind, n),
                    (Kind::Bang, None) => i64::from(n == 0),
                    _ => unreachable!(),
                })
            }
            ExprKind::Assign(slot, arg) => {
                let value = value!(self.expr(arg, frame));
                self.consume(arg, frame);
                if !self.erased_local(*slot, frame) {
                    self.drop_resource(
                        self.program.functions[frame.function].local_resources[*slot],
                        frame,
                    )?;
                    self.store_local(*slot, value, frame);
                    self.local_active(*slot, frame);
                }
                Value::Scalar(0)
            }
            ExprKind::RefAssign(reference_expr, offset, replacement) => {
                let reference = value!(self.expr(reference_expr, frame));
                let replacement = value!(self.expr(replacement, frame));
                let Value::RecordRef(cell) = reference else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: record field write has no record reference",
                    ));
                };
                let pointer = reference_expr
                    .ty
                    .ref_pointee()
                    .expect("checked record reference");
                let ty = self.program.pointees[pointer];
                let mut whole = cell.lock().unwrap();
                if !assign_project(
                    &self.program.enums,
                    &self.program.unions,
                    &self.program.function_types,
                    ty,
                    &mut whole,
                    *offset,
                    replacement,
                ) {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: record field write has no matching field",
                    ));
                }
                Value::Scalar(0)
            }
            ExprKind::Binary(op, left, right) => {
                let left_float = left.ty.float_kind();
                let left_kind = left.ty.int_kind();
                let left = value!(self.expr(left, frame)).scalar();
                if *op == Kind::AmpAmp && left == 0 {
                    return Ok(Flow::Value(Value::Scalar(0)));
                }
                if *op == Kind::PipePipe && left != 0 {
                    return Ok(Flow::Value(Value::Scalar(1)));
                }
                let right_kind = right.ty.int_kind();
                let right = value!(self.expr(right, frame)).scalar();
                if let Some(kind) = left_float {
                    return Ok(Flow::Value(Value::Scalar(match op {
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne => {
                            i64::from(crate::float::compare(kind, op, left, right))
                        }
                        _ => crate::float::binary(kind, op, left, right),
                    })));
                }
                if let Some(kind) = left_kind {
                    return Ok(Flow::Value(Value::Scalar(match op {
                        Kind::Lt | Kind::Le | Kind::Gt | Kind::Ge | Kind::EqEq | Kind::Ne => {
                            i64::from(crate::int::compare(kind, op, left, right))
                        }
                        _ => {
                            let shift = right_kind.map_or(0, |k| k.decode(right));
                            crate::int::binary(kind, op, left, right, shift).ok_or_else(panic)?
                        }
                    })));
                }
                Value::Scalar(match op {
                    Kind::Plus => left.checked_add(right).ok_or_else(panic)?,
                    Kind::Minus => left.checked_sub(right).ok_or_else(panic)?,
                    Kind::Star => left.checked_mul(right).ok_or_else(panic)?,
                    Kind::Slash => left.checked_div(right).ok_or_else(panic)?,
                    Kind::Percent => left.checked_rem(right).ok_or_else(panic)?,
                    Kind::Lt => i64::from(left < right),
                    Kind::Le => i64::from(left <= right),
                    Kind::Gt => i64::from(left > right),
                    Kind::Ge => i64::from(left >= right),
                    Kind::EqEq => i64::from(left == right),
                    Kind::Ne => i64::from(left != right),
                    Kind::AmpAmp | Kind::PipePipe => i64::from(right != 0),
                    _ => unreachable!(),
                })
            }
            ExprKind::VecMap {
                vector,
                callbacks,
                source: _,
                target: _,
            } => {
                let Value::Owned(id) = value!(self.expr(vector, frame)) else {
                    unreachable!("checked map vector")
                };
                let mut functions = Vec::with_capacity(callbacks.len());
                for callback in callbacks {
                    functions.push(value!(self.expr(callback, frame)));
                }
                self.consume(vector, frame);
                for callback in callbacks {
                    self.consume(callback, frame);
                }
                return self.vec_map_call(id, functions, expr.span).map(Flow::Value);
            }
            ExprKind::Call(target, args) => {
                let mut values = Vec::new();
                for arg in args {
                    values.push(value!(self.expr(arg, frame)));
                }
                for arg in args {
                    self.consume(arg, frame);
                }
                match target {
                    Target::Io(op, shape) => self.io_call(*op, *shape, values, expr.span)?,
                    Target::Bytes(op) => self.bytes_call(*op, values, expr.span)?,
                    Target::String(op) => self.string_call(*op, values, expr.span)?,
                    Target::Str(op) => self.str_call(*op, values, expr.span)?,
                    Target::Vec(op, _) => self.vec_call(*op, values, expr.span)?,
                    Target::Slice(op, _) => self.slice_call(*op, values, expr.span)?,
                    Target::Function(index) => self.call(*index, values)?,
                    Target::Panic => return Err(panic()),
                    Target::Print => {
                        writeln!(self.output, "{}", values[0].scalar()).map_err(|e| {
                            Diagnostic::new(expr.span, format!("output failed: {e}"))
                        })?;
                        Value::Scalar(0)
                    }
                    Target::PrintInt(kind) => {
                        writeln!(self.output, "{}", kind.decode(values[0].scalar())).map_err(
                            |e| Diagnostic::new(expr.span, format!("output failed: {e}")),
                        )?;
                        Value::Scalar(0)
                    }
                    Target::PrintFloat(kind) => {
                        writeln!(
                            self.output,
                            "{}",
                            crate::float::format(*kind, values[0].scalar())
                        )
                        .map_err(|e| Diagnostic::new(expr.span, format!("output failed: {e}")))?;
                        Value::Scalar(0)
                    }
                    Target::Float(op) => {
                        let words = values.iter().map(Value::scalar).collect::<Vec<_>>();
                        let (present, word) = crate::float::builtin(*op, &words);
                        use crate::float::FloatOp;
                        match op {
                            FloatOp::TryFromInt {
                                some_tag, none_tag, ..
                            }
                            | FloatOp::TryToF32 {
                                some_tag, none_tag, ..
                            }
                            | FloatOp::TryToInt {
                                some_tag, none_tag, ..
                            } => Value::Enum {
                                tag: if present { *some_tag } else { *none_tag },
                                fields: if present {
                                    vec![Value::Scalar(word)]
                                } else {
                                    vec![]
                                },
                            },
                            _ => Value::Scalar(word),
                        }
                    }
                    Target::Int(op, source, target) => {
                        let words = values.iter().map(Value::scalar).collect::<Vec<_>>();
                        let (present, word) = crate::int::builtin(*op, *source, *target, &words);
                        use crate::int::IntOp;
                        match op {
                            IntOp::TryConvert { some_tag, none_tag }
                            | IntOp::Checked(_, some_tag, none_tag)
                            | IntOp::CharFromCode { some_tag, none_tag } => Value::Enum {
                                tag: if present { *some_tag } else { *none_tag },
                                fields: if present {
                                    vec![Value::Scalar(word)]
                                } else {
                                    vec![]
                                },
                            },
                            _ => Value::Scalar(word),
                        }
                    }
                }
            }
            ExprKind::Return(arg) => {
                let value = value!(self.expr(arg, frame));
                self.consume(arg, frame);
                self.cleanup(frame)?;
                return Ok(Flow::Return(value));
            }
            ExprKind::If(condition, yes, no) => {
                let condition = value!(self.expr(condition, frame)).scalar();
                return self.block(if condition != 0 { yes } else { no }, frame);
            }
            ExprKind::Match(input, arms) => {
                let value = value!(self.expr(input, frame));
                for arm in arms {
                    if pattern_matches(&arm.pattern, &value, &mut frame.locals) {
                        if let Some(guard) = &arm.guard
                            && value!(self.expr(guard, frame)).scalar() == 0
                        {
                            continue;
                        }
                        self.consume(input, frame);
                        self.activate_pattern(&arm.pattern, &value, frame)?;
                        let result = match self.expr(&arm.body, frame)? {
                            Flow::Value(v) => v,
                            other => {
                                // break/continue/return leave the arm; its bindings are
                                // cleaned by the exit's cleanup list or by return.
                                return Ok(other);
                            }
                        };
                        self.consume(&arm.body, frame);
                        let mut slots = std::collections::BTreeSet::new();
                        crate::ownership::pattern_bindings(&arm.pattern, &mut slots);
                        for slot in slots.into_iter().rev() {
                            self.drop_resource(
                                self.program.functions[frame.function].local_resources[slot],
                                frame,
                            )?;
                        }
                        return Ok(Flow::Value(result));
                    }
                }
                unreachable!("exhaustiveness checked")
            }
        };
        Ok(Flow::Value(result))
    }
    fn activate_pattern(
        &mut self,
        pattern: &Pattern,
        value: &Value,
        frame: &mut Frame,
    ) -> Result<()> {
        match pattern {
            Pattern::Any => self.drop_value(value.clone())?,
            Pattern::Bind(slot) => self.local_active(*slot, frame),
            Pattern::Variant { fields, .. } => {
                let Value::Enum { fields: values, .. } = value else {
                    unreachable!()
                };
                for ((_, p), v) in fields.iter().zip(values).rev() {
                    self.activate_pattern(p, v, frame)?;
                }
            }
            Pattern::Type { tag, inner, .. } => {
                let Value::Union { tag: actual, value } = value else {
                    unreachable!()
                };
                if actual == tag {
                    self.activate_pattern(inner, value, frame)?;
                }
            }
            Pattern::Or(ps) => {
                let p = ps.iter().find(|p| pattern_test(p, value)).unwrap();
                self.activate_pattern(p, value, frame)?;
            }
            _ => {}
        }
        Ok(())
    }
}
fn pattern_test(pattern: &Pattern, value: &Value) -> bool {
    match pattern {
        Pattern::Any | Pattern::Bind(_) => true,
        Pattern::Literal(n) => value.scalar() == *n,
        Pattern::Or(ps) => ps.iter().any(|p| pattern_test(p, value)),
        Pattern::Variant { tag, fields } => {
            let Value::Enum {
                tag: actual,
                fields: values,
            } = value
            else {
                unreachable!()
            };
            tag == actual
                && fields
                    .iter()
                    .zip(values)
                    .all(|((_, p), v)| pattern_test(p, v))
        }
        Pattern::Type { tag, inner, .. } => {
            let Value::Union { tag: actual, value } = value else {
                return false;
            };
            tag == actual && pattern_test(inner, value)
        }
    }
}
fn pattern_matches(pattern: &Pattern, value: &Value, locals: &mut [Value]) -> bool {
    if !pattern_test(pattern, value) {
        return false;
    }
    match pattern {
        Pattern::Bind(slot) => locals[*slot] = value.clone(),
        Pattern::Variant { fields, .. } => {
            let Value::Enum { fields: values, .. } = value else {
                unreachable!()
            };
            for ((_, p), v) in fields.iter().zip(values) {
                pattern_matches(p, v, locals);
            }
        }
        Pattern::Type { tag, inner, .. } => {
            let Value::Union { tag: actual, value } = value else {
                unreachable!()
            };
            if actual == tag {
                pattern_matches(inner, value, locals);
            }
        }
        Pattern::Or(ps) => {
            let p = ps.iter().find(|p| pattern_test(p, value)).unwrap();
            pattern_matches(p, value, locals);
        }
        _ => {}
    }
    true
}

/// Copy the field at a word offset out of a record value.
fn project(
    enums: &[crate::runtime_types::Enum],
    unions: &[crate::runtime_types::UnionType],
    functions: &[crate::runtime_types::FunctionType],
    ty: Type,
    value: Value,
    offset: usize,
) -> Value {
    let Value::Enum { fields, .. } = value else {
        unreachable!("projection from a record")
    };
    let id = ty.layout().unwrap();
    let mut at = 1;
    for (field, field_ty) in fields.into_iter().zip(&enums[id].variants[0].fields) {
        if at == offset {
            return field;
        }
        at += crate::runtime_types::width(enums, unions, functions, *field_ty);
    }
    unreachable!("checked field offset")
}
/// Store a checked copyable field through a record reference. `offset` is a
/// word offset from the record tag; nested copyable record paths are handled by
/// recursing instead of flattening or copying the whole owner.
fn assign_project(
    enums: &[crate::runtime_types::Enum],
    unions: &[crate::runtime_types::UnionType],
    functions: &[crate::runtime_types::FunctionType],
    ty: Type,
    value: &mut Value,
    offset: usize,
    replacement: Value,
) -> bool {
    let Value::Enum { fields, .. } = value else {
        return false;
    };
    let id = ty.layout().unwrap();
    let mut at = 1;
    for (index, field_ty) in enums[id].variants[0].fields.iter().enumerate() {
        let width = crate::runtime_types::width(enums, unions, functions, *field_ty);
        if at == offset {
            fields[index] = replacement;
            return true;
        }
        if offset >= at && offset < at + width {
            return assign_project(
                enums,
                unions,
                functions,
                *field_ty,
                &mut fields[index],
                offset - at,
                replacement,
            );
        }
        at += width;
    }
    false
}
