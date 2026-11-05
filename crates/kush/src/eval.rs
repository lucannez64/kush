//! Bounded reference evaluator for checked executable IR. It shares no
//! execution logic with the native backend; tests compare the two.
use crate::grades::Grade;
use crate::{Diagnostic, Span, executable::*, lexer::Kind, runtime_types::ResultShape};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::{self, Cursor, Read, Write},
    net::{Shutdown, TcpStream, ToSocketAddrs},
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicU8, AtomicUsize, Ordering},
        mpsc::{self, Receiver, Sender},
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};
type Result<T> = std::result::Result<T, Diagnostic>;
/// Stack size of a reference-evaluator task thread.
const TASK_STACK_BYTES: usize = 64 * 1024 * 1024;

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
        self.evaluate_with_io_limits(input, output, None, &Host::empty())
    }
    /// Reference evaluation with explicit standard streams and host inputs.
    /// Native programs always observe the real process; this entry point makes
    /// arguments and environment observable and testable without global state.
    pub fn evaluate_with_host(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        host: &Host,
    ) -> Result<i64> {
        self.evaluate_with_host_and_stats(input, output, host)
            .map(|(value, _)| value)
    }
    pub fn evaluate_with_host_and_stats(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        host: &Host,
    ) -> Result<(i64, MemoryStats)> {
        self.evaluate_with_io_limits(input, output, None, host)
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
        self.evaluate_with_io_limits(&mut io::empty(), output, Some(budget), &Host::empty())
    }
    fn evaluate_with_io_limits(
        &self,
        input: &mut dyn Read,
        output: &mut dyn Write,
        alloc_budget: Option<usize>,
        host: &Host,
    ) -> Result<(i64, MemoryStats)> {
        if self.uses_tasks {
            return self.evaluate_tasks(input, output, alloc_budget, host);
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
            dynamic_handlers: Vec::new(),
            try_budget: alloc_budget.map(|budget| Arc::new(AtomicUsize::new(budget))),
            host: Arc::new(host.clone()),
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
        host: &Host,
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
            Arc::new(host.clone()),
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
    #[allow(clippy::too_many_arguments)]
    fn run_scheduler(
        &self,
        entry: usize,
        heap: SharedHeap,
        stats: StatsHandle,
        source: SharedInput,
        sink: SharedWriter,
        try_budget: Option<Arc<AtomicUsize>>,
        host: Arc<Host>,
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
                &host,
                entry,
                None,
                Vec::new(),
                false,
                Vec::new(),
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
                        handlers,
                    } => {
                        let child = self.start_task(
                            scope,
                            &mut records,
                            &heap,
                            &stats,
                            &source,
                            &sink,
                            &try_budget,
                            &host,
                            function,
                            environment,
                            Vec::new(),
                            preserve,
                            handlers,
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
                    dynamic_handlers: Vec::new(),
                    try_budget: try_budget.clone(),
                    host: host.clone(),
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
        host: &Arc<Host>,
        function: usize,
        environment: Option<usize>,
        arguments: Vec<Value>,
        preserve: bool,
        handlers: Vec<(usize, usize)>,
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
            dynamic_handlers: handlers
                .into_iter()
                .map(|(operation, function)| HandlerFrame {
                    operation,
                    handler: Some(Value::Function {
                        function,
                        environment: None,
                    }),
                    redirect: None,
                    consume: false,
                })
                .collect(),
            try_budget: try_budget.clone(),
            host: host.clone(),
        };
        stats.allocation();
        stats.allocation();
        // Task threads get the main thread's stack budget: the reference
        // evaluator's nesting limit assumes it, and the default 2 MiB thread
        // stack overflowed a few nested task scopes in debug builds. Only the
        // pages actually used are committed.
        let task = thread::Builder::new()
            .name(format!("kush-task-{id}"))
            .stack_size(TASK_STACK_BYTES);
        let spawned = task.spawn_scoped(scope, move || {
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
        // Like `Scope::spawn`, failing to create the thread is fatal.
        spawned.expect("failed to start a reference evaluator task thread");
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
fn os_bytes(value: OsString) -> Vec<u8> {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        value.into_vec()
    }
    #[cfg(not(unix))]
    {
        value.to_string_lossy().into_owned().into_bytes()
    }
}
fn value_bytes(value: &[u8]) -> OsString {
    #[cfg(unix)]
    {
        use std::os::unix::ffi::OsStringExt;
        OsString::from_vec(value.to_vec())
    }
    #[cfg(not(unix))]
    {
        OsString::from(String::from_utf8_lossy(value).into_owned())
    }
}
fn path_from_bytes(value: &[u8]) -> PathBuf {
    PathBuf::from(value_bytes(value))
}
/// Split a NUL-separated argument encoding, ignoring empty segments and a
/// trailing NUL exactly like the native subprocess path.
fn split_nul(value: &[u8]) -> Vec<OsString> {
    let mut arguments = Vec::new();
    let mut start = 0;
    for index in 0..=value.len() {
        if index == value.len() || value[index] == 0 {
            if index > start {
                arguments.push(value_bytes(&value[start..index]));
            }
            start = index + 1;
        }
    }
    arguments
}
fn exit_status_code(status: std::process::ExitStatus) -> i64 {
    if let Some(code) = status.code() {
        return i64::from(code);
    }
    #[cfg(unix)]
    {
        use std::os::unix::process::ExitStatusExt;
        128 + status.signal().map_or(0, i64::from)
    }
    #[cfg(not(unix))]
    {
        128
    }
}
/// Host inputs visible to the reference evaluator. Native executables read the
/// real process arguments and environment; tests and tooling use this value to
/// provide explicit, deterministic inputs instead. `evaluate_with_io` and
/// `evaluate` use an empty host, while `Host::process` mirrors the CLI process.
#[derive(Debug, Clone)]
pub struct Host {
    args: Arc<Vec<Vec<u8>>>,
    environment: Arc<BTreeMap<Vec<u8>, Vec<u8>>>,
    monotonic_origin: Instant,
}
impl Default for Host {
    fn default() -> Self {
        Self::empty()
    }
}
impl Host {
    /// No arguments and no environment variables. This is the deterministic
    /// default for existing reference evaluation entry points.
    pub fn empty() -> Self {
        Self {
            args: Arc::new(Vec::new()),
            environment: Arc::new(BTreeMap::new()),
            monotonic_origin: Instant::now(),
        }
    }
    /// The current process arguments (including argv[0]) and environment.
    pub fn process() -> Self {
        let args = std::env::args_os().map(os_bytes).collect();
        let environment = std::env::vars_os()
            .map(|(name, value)| (os_bytes(name), os_bytes(value)))
            .collect();
        Self {
            args: Arc::new(args),
            environment: Arc::new(environment),
            monotonic_origin: Instant::now(),
        }
    }
    /// Replace argv while retaining this host's environment and clock origin.
    pub fn with_args(mut self, args: Vec<Vec<u8>>) -> Self {
        self.args = Arc::new(args);
        self
    }
    /// Explicit raw-byte arguments and environment entries. Later duplicate
    /// names replace earlier ones.
    pub fn new(args: Vec<Vec<u8>>, environment: Vec<(Vec<u8>, Vec<u8>)>) -> Self {
        Self {
            args: Arc::new(args),
            environment: Arc::new(environment.into_iter().collect()),
            monotonic_origin: Instant::now(),
        }
    }
    fn var(&self, name: &[u8]) -> Option<&[u8]> {
        self.environment.get(name).map(Vec::as_slice)
    }
    fn monotonic_ns(&self) -> i64 {
        let elapsed = self.monotonic_origin.elapsed();
        (elapsed.as_nanos().min(i64::MAX as u128)) as i64
    }
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
/// Mirror the native small-block classes for initial/infallible box storage.
fn box_allocation_capacity(bytes: usize) -> usize {
    if bytes <= 1024 {
        bytes.max(1).next_multiple_of(16)
    } else {
        bytes
    }
}
/// Reference model of the native arena bump requirement: an eight-byte arena
/// box header followed by the payload, rounded up to the 16-byte alignment.
fn arena_round(bytes: usize) -> usize {
    (bytes.saturating_add(8)).div_ceil(16) * 16
}

#[derive(Debug, Clone)]
struct HeapState {
    map: BTreeMap<usize, Value>,
    /// Usable native payload bytes for boxes, independent of their current
    /// logical payload type. Narrowing reuse must not discard this capacity.
    box_capacities: BTreeMap<usize, usize>,
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
            box_capacities: BTreeMap::new(),
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
        let mut state = self.0.lock().unwrap();
        state.box_capacities.remove(&id);
        state.map.remove(&id)
    }
    fn box_capacity(&self, id: usize) -> usize {
        self.0.lock().unwrap().box_capacities[&id]
    }
    fn set_box_capacity(&self, id: usize, bytes: usize) {
        self.0.lock().unwrap().box_capacities.insert(id, bytes);
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
    /// Modelled bytes consumed in the current chunk. Native chunks are
    /// physical storage and are not counted as logical allocations.
    chunk_used: usize,
    /// Capacity of the current chunk in payload bytes, including the box
    /// header and alignment padding.
    chunk_capacity: usize,
    /// Optional user chunk-sizing strategy. The function value is a
    /// noncapturing code pointer, so it cannot capture or dangle.
    strategy: Option<usize>,
}
/// The allocator recorded by one container. A legacy value is three checked
/// code pointers and owns nothing; an instance context owns a reference to the
/// compiler-owned state cell and calls the selected protocol methods.
#[derive(Debug, Clone)]
enum AllocatorBinding {
    Static {
        alloc: usize,
        free: usize,
        realloc: Option<usize>,
    },
    Context(Arc<AllocatorContextState>),
}
/// One reference-counted allocator instance. `instance` is the concrete state
/// value; `alloc`, `free`, and `grow` are checked `&mut Self` method functions.
/// The count is explicit because sharing is the checked
/// `AllocatorContext.share` operation, never an implicit clone of an affine
/// value.
#[derive(Debug)]
struct AllocatorContextState {
    references: std::sync::atomic::AtomicUsize,
    instance: Arc<Mutex<Value>>,
    alloc: usize,
    free: usize,
    grow: usize,
}
/// Heap state of one `AllocBox<T>`. Boxed inside `Value` so the enum stays
/// small: deeply recursive reference evaluation depends on a compact frame.
#[derive(Debug, Clone)]
struct AllocBoxState {
    allocator: AllocatorBinding,
    block: Value,
    payload: Value,
}
/// Heap state of one `AllocVec<T>`. Boxed for the same reason.
#[derive(Debug, Clone)]
struct AllocVectorState {
    items: Vec<Value>,
    capacity: usize,
    allocator: AllocatorBinding,
    block: Option<Value>,
}
/// One borrowed slice view. Boxed inside `Value` so adding field-view
/// provenance does not grow every recursive evaluator frame.
#[derive(Debug, Clone)]
struct SliceValue {
    base: Box<Value>,
    start: usize,
    len: usize,
    array: Option<Arc<Mutex<Value>>>,
    /// When the view is over a `DynArray` field of a record, the field index
    /// path from the pinned record root in `array` (or from the referent of
    /// `reference`).
    field: Option<Vec<usize>>,
    /// A view over a `DynArray` field reached through a checked record
    /// reference: the reference value itself. Reads go through the referent and
    /// writes store the updated referent back without dropping anything.
    reference: Option<Box<Value>>,
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
        /// Retained native allocation bytes, including the three-word header.
        usable: usize,
    },
    /// An immutable or exclusive slice view: `start` is in elements of the
    /// underlying storage. `array` is a shared cell used when the base is an
    /// inline array local, so writes through `&mut [T]` are visible to the
    /// owner. The base is a borrowed Vec/Bytes handle and is never itself a
    /// `Slice` (sub-slices are flattened).
    Slice(Box<SliceValue>),
    /// An inline array local whose storage has been pinned in a shared cell so
    /// a mutable slice view can alias it. Reads materialize a fresh array value.
    ArrayCell(Arc<Mutex<Value>>),
    /// A scalar local whose address was captured by a live-view closure. Reads
    /// materialize the current value and writes go through the cell, so the
    /// closure and its caller observe one location.
    ScalarCell(Arc<Mutex<Value>>),
    /// A nominal-record local promoted to shared storage so a call-scoped
    /// `&Record`/`&mut Record` can point at it. Reads materialize the current
    /// record value; writes through an exclusive reference update this cell.
    RecordCell(Arc<Mutex<Value>>),
    /// A checked call-scoped record reference. It aliases the owning local's
    /// pinned cell and never owns the record or its fields.
    RecordRef(Arc<Mutex<Value>>),
    /// A checked reference to a projected place inside a pinned local
    /// aggregate. `steps` records each relative word offset together with the
    /// aggregate type that contains it, so reads and writes navigate the live
    /// value rather than a copy. It owns nothing.
    PlaceRef {
        root: Arc<Mutex<Value>>,
        steps: Vec<(usize, Type)>,
    },
    /// A checked reference to one element of an owned `Vec<T>` local or field.
    /// `steps` are relative field offsets inside that element. The vector owner
    /// remains loaned for the reference's checked last use, so the element
    /// never moves while the reference is live.
    ElementRef {
        owner: usize,
        index: usize,
        steps: Vec<(usize, Type)>,
    },
    /// A checked reference to one element of a slice view. Reads and writes
    /// go through the view's own storage (an array cell, a DynArray, a record
    /// field, or a vector), so the owner observes every write; `steps` are
    /// relative field offsets inside the element. It owns nothing.
    SliceElementRef {
        view: Box<Value>,
        index: usize,
        steps: Vec<(usize, Type)>,
    },
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
    /// Runtime-sized inline array: `items.len()` is the current length and
    /// `capacity` is the static bound. Only `items` is initialized.
    DynArray {
        items: Vec<Value>,
        capacity: usize,
    },
    /// A checked user allocator value: the noncapturing function handles
    /// for allocation and release. It owns nothing and is copyable.
    Allocator {
        alloc: usize,
        free: usize,
        /// Optional growth hook function index; index zero is a valid hook.
        realloc: Option<usize>,
    },
    /// An owning reference to one allocator instance. The context state holds
    /// the concrete instance value and its checked method indices. The last
    /// reference drops the instance exactly once.
    AllocatorContext(Arc<AllocatorContextState>),
    /// A temporary `&AllocatorContext` borrow used only by
    /// `AllocatorContext.share`; it never owns a reference.
    AllocatorContextRef(Arc<AllocatorContextState>),
    /// The heap state of one `AllocBox<T>`: the allocator pair, the `Bytes`
    /// block that owns the payload storage, and the payload itself. The
    /// reference evaluator models payload storage separately, but the block is
    /// a real owned allocation released through the user callback exactly once.
    AllocBox(Box<AllocBoxState>),
    /// The heap state of one `AllocVec<T>`. `block` is the allocator-supplied
    /// `Bytes` storage; `items` models the live elements. Growth allocates a
    /// fresh block and releases the old one through the same allocator.
    AllocVector(Box<AllocVectorState>),
    /// An opaque structured-task handle. The handle owns no heap cell; scope
    /// completion joins the child exactly once.
    Task(usize),
    /// A temporary `&Task<T>` borrow used only by `Task.cancel`.
    TaskRef(usize),
    /// An open/generic trait object: the registered member identifier and the
    /// owned payload cell. The cell lets a borrowed `&dyn`/`&mut dyn` dispatch
    /// pass the same storage to the concrete method without copying.
    DynObject {
        member: usize,
        value: Arc<Mutex<Value>>,
    },
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
/// A resolved checked place: either a path into a pinned local aggregate or a
/// path into one element of an owned vector. It is not a runtime value; the
/// borrow expression converts it into a `Value::PlaceRef`/`ElementRef` handle.
#[derive(Debug, Clone)]
enum ResolvedPlace {
    Cell {
        root: Arc<Mutex<Value>>,
        steps: Vec<(usize, Type)>,
        ty: Type,
    },
    Element {
        owner: usize,
        index: usize,
        steps: Vec<(usize, Type)>,
        ty: Type,
    },
    SliceElement {
        view: Box<Value>,
        index: usize,
        steps: Vec<(usize, Type)>,
        ty: Type,
    },
}
/// Result of resolving an addressable place. A temporary-owner initializer at
/// a place root may itself `return`, `break`, `continue`, or `?`; those flows
/// must reach the surrounding expression instead of becoming a place error.
enum PlaceFlow {
    Place(ResolvedPlace),
    Value(Value),
    Return(Value),
    Break(Value),
    Continue,
    Exit(Value, bool),
}
impl From<Flow> for PlaceFlow {
    fn from(flow: Flow) -> Self {
        match flow {
            Flow::Value(value) => PlaceFlow::Value(value),
            Flow::Return(value) => PlaceFlow::Return(value),
            Flow::Break(value) => PlaceFlow::Break(value),
            Flow::Continue => PlaceFlow::Continue,
            Flow::Exit(value, finish) => PlaceFlow::Exit(value, finish),
        }
    }
}
#[derive(Debug)]
enum Flow {
    Value(Value),
    Return(Value),
    Break(Value),
    Continue,
    /// Leave the innermost `Region`; the flag applies the region's finish.
    Exit(Value, bool),
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
        /// Inheritable dynamic handler frames: `(operation, function)` pairs
        /// for copyable noncapturing `fn` handlers. Capturing or one-shot
        /// frames are a task boundary and are not inherited.
        handlers: Vec<(usize, usize)>,
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
        handlers: Vec<(usize, usize)>,
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
                handlers,
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
/// One dynamic handler frame. `handler` is `None` after a one-shot handler has
/// been consumed by a `perform`; the frame stays until its lexical pop so an
/// inner consumed frame correctly uncovers an outer handler.
struct HandlerFrame {
    operation: usize,
    handler: Option<Value>,
    /// A redirect frame: lookups continue below this depth instead.
    redirect: Option<usize>,
    /// A `once` handler owns its environment and can be consumed only once.
    /// A copyable `fn` handler serves any number of performs.
    consume: bool,
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
    /// Dynamically scoped handlers for declared effect operations. The stack is
    /// unwound on every normal or early exit from the handled body, dropping an
    /// unconsumed owning handler exactly once.
    dynamic_handlers: Vec<HandlerFrame>,
    /// Remaining successful fallible allocation attempts for deterministic
    /// failure probes. `None` means unlimited.
    try_budget: Option<Arc<AtomicUsize>>,
    /// Injected arguments/environment and the monotonic clock origin. Native
    /// execution reads the real process instead.
    host: Arc<Host>,
}
macro_rules! value {
    ($e:expr) => {
        match $e? {
            Flow::Value(v) => v,
            returned => return Ok(returned),
        }
    };
}
/// Redeem a checked-place evaluation into its reference value, propagating a
/// `return`/`break`/`continue` that originated in a temporary-owner
/// initializer at the place root.
macro_rules! place_value {
    ($e:expr) => {
        match $e? {
            PlaceFlow::Value(v) => v,
            PlaceFlow::Return(v) => return Ok(Flow::Return(v)),
            PlaceFlow::Break(v) => return Ok(Flow::Break(v)),
            PlaceFlow::Continue => return Ok(Flow::Continue),
            PlaceFlow::Exit(v, finish) => return Ok(Flow::Exit(v, finish)),
            PlaceFlow::Place(_) => unreachable!("a place evaluation has no ordinary place flow"),
        }
    };
}
impl<R: Read, W: Write> Evaluator<'_, R, W> {
    fn allocate(&mut self, payload: Value) -> Value {
        let id = self.heap.allocate(payload);
        self.stats.allocation();
        Value::Owned(id)
    }
    fn allocate_box(&mut self, payload: Value, words: usize) -> Value {
        let value = self.allocate(payload);
        let Value::Owned(id) = value else {
            unreachable!()
        };
        self.heap
            .set_box_capacity(id, box_allocation_capacity(words * 8));
        value
    }
    /// Extract the recorded allocator from a checked allocator value. The
    /// context variant transfers its reference to the caller; the caller must
    /// either store it in a container or release it.
    fn allocator_binding(&mut self, value: Value, span: Span) -> Result<AllocatorBinding> {
        match value {
            Value::Allocator {
                alloc,
                free,
                realloc,
            } => Ok(AllocatorBinding::Static {
                alloc,
                free,
                realloc,
            }),
            // The context's heap cell is only the owning handle; transferring
            // the reference to a container releases the cell itself.
            Value::AllocatorContext(state) => Ok(AllocatorBinding::Context(state)),
            Value::Owned(id) => match self.heap.take(id) {
                Some(Value::AllocatorContext(state)) => {
                    self.stats.deallocation();
                    Ok(AllocatorBinding::Context(state))
                }
                other => {
                    if let Some(value) = other {
                        self.heap.insert(id, value);
                    }
                    Err(Diagnostic::new(
                        span,
                        "internal error: expected a checked allocator context",
                    ))
                }
            },
            _ => Err(Diagnostic::new(
                span,
                "internal error: expected a checked allocator value",
            )),
        }
    }
    /// One context method call with the shared instance as its `&mut self`
    /// receiver. The instance cell is pinned, so mutations are visible to every
    /// later call through the same context.
    fn allocator_context_call(
        &mut self,
        state: &AllocatorContextState,
        function: usize,
        arguments: Vec<Value>,
    ) -> Result<Value> {
        let mut values = Vec::with_capacity(arguments.len() + 1);
        values.push(Value::RecordRef(state.instance.clone()));
        values.extend(arguments);
        self.call(function, values)
    }
    /// Ask a user allocator for a block of `bytes` payload storage. `None`
    /// means the callback returned a block that cannot hold the request; that
    /// block is released through the same release callback before the refusal
    /// is reported, so a refusal never leaks storage.
    fn allocator_block(
        &mut self,
        allocator: &AllocatorBinding,
        bytes: usize,
        span: Span,
    ) -> Result<Option<Value>> {
        let block = match allocator {
            AllocatorBinding::Static { alloc, .. } => {
                self.call(*alloc, vec![Value::Scalar(bytes as i64)])?
            }
            AllocatorBinding::Context(state) => {
                self.allocator_context_call(state, state.alloc, vec![Value::Scalar(bytes as i64)])?
            }
        };
        let capacity = self.allocator_block_capacity(&block, span)?;
        if capacity >= bytes {
            Ok(Some(block))
        } else {
            self.allocator_release(allocator, block, span)?;
            Ok(None)
        }
    }
    fn allocator_block_capacity(&self, block: &Value, span: Span) -> Result<usize> {
        match block {
            Value::Owned(id) => match self.heap.get(*id) {
                Some(Value::Buffer { capacity, .. }) => Ok(capacity),
                _ => Err(Diagnostic::new(
                    span,
                    "internal error: allocator callback did not return a Bytes block",
                )),
            },
            _ => Err(Diagnostic::new(
                span,
                "internal error: allocator callback did not return an owned Bytes block",
            )),
        }
    }
    /// Release one allocator-supplied block through its recorded release
    /// function. The callback consumes the `Bytes` owner, so the underlying
    /// allocation is freed exactly once.
    fn allocator_release(
        &mut self,
        allocator: &AllocatorBinding,
        block: Value,
        span: Span,
    ) -> Result<()> {
        match allocator {
            AllocatorBinding::Static { free, .. } => {
                let _ = self.call(*free, vec![block])?;
            }
            AllocatorBinding::Context(state) => {
                let _ = self.allocator_context_call(state, state.free, vec![block])?;
            }
        }
        let _ = span;
        Ok(())
    }
    /// Ask a user growth hook to resize one block. The callback consumes the
    /// previous block and must return a block with at least `bytes` capacity;
    /// a smaller result is a panic because the old block is already gone.
    fn allocator_realloc_block(
        &mut self,
        allocator: &AllocatorBinding,
        mut block: Value,
        old_bytes: usize,
        bytes: usize,
        span: Span,
    ) -> Result<Value> {
        // The evaluator models an allocator block as zero-initialized byte
        // storage; expose `old_bytes` readable bytes so a copying growth hook
        // behaves the same way as in the native backend.
        if let Value::Owned(id) = block
            && let Some(Value::Buffer { mut data, capacity }) = self.heap.get(id)
        {
            data.clear();
            data.resize(old_bytes, 0);
            self.heap.insert(id, Value::Buffer { data, capacity });
            block = Value::Owned(id);
        }
        let arguments = vec![
            block,
            Value::Scalar(old_bytes as i64),
            Value::Scalar(bytes as i64),
        ];
        let grown = match allocator {
            AllocatorBinding::Static {
                realloc: Some(realloc),
                ..
            } => self.call(*realloc, arguments)?,
            AllocatorBinding::Context(state) => {
                self.allocator_context_call(state, state.grow, arguments)?
            }
            AllocatorBinding::Static { realloc: None, .. } => {
                return Err(Diagnostic::new(
                    span,
                    "internal error: no recorded allocator growth hook",
                ));
            }
        };
        let capacity = self.allocator_block_capacity(&grown, span)?;
        if capacity < bytes {
            return Err(Diagnostic::new(
                span,
                format!("panic: allocator growth hook returned a block smaller than {bytes} bytes"),
            ));
        }
        Ok(grown)
    }
    /// Drop one allocator-context reference. The last reference destroys the
    /// retained instance value exactly once and releases the compiler-owned
    /// context and state cells.
    fn allocator_context_release(&mut self, state: &Arc<AllocatorContextState>) -> Result<()> {
        use std::sync::atomic::Ordering;
        if state.references.fetch_sub(1, Ordering::SeqCst) != 1 {
            return Ok(());
        }
        let instance = std::mem::replace(&mut *state.instance.lock().unwrap(), Value::Scalar(0));
        self.drop_value(instance)?;
        // The state cell is compiler-owned bookkeeping; the owning context
        // handle is a normal heap cell and is counted when it is dropped.
        self.stats.deallocation();
        Ok(())
    }
    fn release_allocator_binding(&mut self, binding: AllocatorBinding) -> Result<()> {
        match binding {
            AllocatorBinding::Static { .. } => Ok(()),
            AllocatorBinding::Context(state) => self.allocator_context_release(&state),
        }
    }
    /// Store an allocator binding and block as one owning metadata cell.
    fn allocate_alloc_box(
        &mut self,
        allocator: AllocatorBinding,
        block: Value,
        payload: Value,
    ) -> Value {
        self.allocate(Value::AllocBox(Box::new(AllocBoxState {
            allocator,
            block,
            payload,
        })))
    }
    /// Evaluate the post-argument part of `AllocBox.new`. Kept out of the
    /// recursive evaluator match so the shared expression frame stays small;
    /// deeply recursive programs rely on that headroom.
    #[inline(never)]
    fn eval_alloc_box_new(
        &mut self,
        allocator: Value,
        payload: Value,
        bytes: usize,
        span: Span,
    ) -> Result<Value> {
        let allocator = self.allocator_binding(allocator, span)?;
        let block = self
            .allocator_block(&allocator, bytes, span)?
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!("panic: allocator refused a {bytes}-byte block"),
                )
            })?;
        Ok(self.allocate_alloc_box(allocator, block, payload))
    }
    #[inline(never)]
    fn eval_alloc_box_try_new(
        &mut self,
        allocator: Value,
        payload: Value,
        bytes: usize,
        shape: ResultShape,
        span: Span,
    ) -> Result<Value> {
        let allocator = self.allocator_binding(allocator, span)?;
        Ok(match self.allocator_block(&allocator, bytes, span)? {
            Some(block) => Value::Enum {
                tag: shape.ok_tag,
                fields: vec![self.allocate_alloc_box(allocator, block, payload)],
            },
            None => {
                // Nothing retained the context on refusal; release the
                // operation's reference so the state is destroyed exactly once.
                self.release_allocator_binding(allocator)?;
                Value::Enum {
                    tag: shape.err_tag,
                    fields: vec![payload],
                }
            }
        })
    }
    #[inline(never)]
    fn eval_alloc_vec_new(
        &mut self,
        allocator: Value,
        capacity: Option<usize>,
        width: usize,
        span: Span,
    ) -> Result<Value> {
        let allocator = self.allocator_binding(allocator, span)?;
        let capacity = capacity.unwrap_or(0);
        let block = if capacity == 0 {
            None
        } else {
            let bytes = capacity
                .checked_mul(width)
                .and_then(|words| words.checked_mul(8))
                .ok_or_else(|| Diagnostic::new(span, "panic: AllocVec capacity overflow"))?;
            Some(
                self.allocator_block(&allocator, bytes, span)?
                    .ok_or_else(|| {
                        Diagnostic::new(
                            span,
                            format!("panic: allocator refused a {bytes}-byte block"),
                        )
                    })?,
            )
        };
        Ok(self.allocate(Value::AllocVector(Box::new(AllocVectorState {
            items: Vec::new(),
            capacity,
            allocator,
            block,
        }))))
    }
    fn arena_new_value(&mut self, strategy: Option<usize>) -> Value {
        self.stats.allocation();
        Value::Arena {
            state: Arc::new(Mutex::new(ArenaState {
                slots: Vec::new(),
                references: 1,
                chunk_used: 0,
                chunk_capacity: 0,
                strategy,
            })),
        }
    }
    /// Choose the capacity of a fresh chunk. The default is the native 4 KiB
    /// minimum; a user strategy receives `(need, current_capacity)` and may
    /// choose any larger capacity. A strategy result below `need` is clamped,
    /// matching the native runtime.
    fn arena_chunk_capacity(
        &mut self,
        state: &Arc<Mutex<ArenaState>>,
        need: usize,
        current: usize,
    ) -> Result<usize> {
        let strategy = state.lock().unwrap().strategy;
        let Some(function) = strategy else {
            return Ok(need.max(4096));
        };
        let chosen = self.call(
            function,
            vec![Value::Scalar(need as i64), Value::Scalar(current as i64)],
        )?;
        let chosen = usize::try_from(chosen.scalar()).unwrap_or(0);
        Ok(chosen.max(need))
    }
    /// Allocate one payload in the region, growing a chunk when the current
    /// bump area cannot fit it. The reference model keeps the region's logical
    /// allocation count unchanged; chunks are physical storage.
    fn arena_allocate(
        &mut self,
        state: &Arc<Mutex<ArenaState>>,
        payload: Value,
        bytes: usize,
    ) -> Result<Value> {
        let need = arena_round(bytes);
        let (needs_chunk, current) = {
            let arena = state.lock().unwrap();
            (
                arena.chunk_capacity.saturating_sub(arena.chunk_used) < need,
                arena.chunk_capacity,
            )
        };
        if needs_chunk {
            let capacity = self.arena_chunk_capacity(state, need, current)?;
            let mut arena = state.lock().unwrap();
            arena.chunk_capacity = capacity;
            arena.chunk_used = 0;
        }
        let mut arena = state.lock().unwrap();
        let slot = arena.slots.len();
        arena.slots.push(Some(payload));
        arena.references += 1;
        arena.chunk_used += need;
        Ok(Value::ArenaBox {
            state: state.clone(),
            slot,
        })
    }
    /// Fallible variant of `arena_allocate`. A refused chunk request spends one
    /// attempt, leaves every region field untouched, and returns the payload in
    /// `Err`; a payload that fits the current chunk spends nothing and cannot
    /// fail.
    fn arena_try_allocate(
        &mut self,
        state: &Arc<Mutex<ArenaState>>,
        payload: Value,
        bytes: usize,
    ) -> Result<std::result::Result<Value, Value>> {
        let need = arena_round(bytes);
        let (needs_chunk, current) = {
            let arena = state.lock().unwrap();
            (
                arena.chunk_capacity.saturating_sub(arena.chunk_used) < need,
                arena.chunk_capacity,
            )
        };
        if needs_chunk {
            if !self.try_charge() {
                return Ok(Err(payload));
            }
            let capacity = self.arena_chunk_capacity(state, need, current)?;
            let mut arena = state.lock().unwrap();
            arena.chunk_capacity = capacity;
            arena.chunk_used = 0;
        }
        let mut arena = state.lock().unwrap();
        let slot = arena.slots.len();
        arena.slots.push(Some(payload));
        arena.references += 1;
        arena.chunk_used += need;
        Ok(Ok(Value::ArenaBox {
            state: state.clone(),
            slot,
        }))
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
        let mut remaining = budget.load(Ordering::SeqCst);
        loop {
            let Some(next) = remaining.checked_sub(1) else {
                return false;
            };
            match budget.compare_exchange_weak(remaining, next, Ordering::SeqCst, Ordering::SeqCst)
            {
                Ok(_) => return true,
                Err(actual) => remaining = actual,
            }
        }
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
            Value::ArrayCell(cell) | Value::RecordCell(cell) | Value::ScalarCell(cell) => {
                *cell.lock().unwrap() = value;
            }
            _ => frame.locals[slot] = value,
        }
    }
    fn materialize(&self, value: Value) -> Value {
        match value {
            Value::ArrayCell(cell) | Value::RecordCell(cell) | Value::ScalarCell(cell) => {
                cell.lock().unwrap().clone()
            }
            value => value,
        }
    }
    /// Pin a mutable scalar local into shared storage and return the captured
    /// location. The closure environment retains only this non-owning cell.
    fn capture_scalar_reference(&self, slot: usize, frame: &mut Frame) -> Value {
        match &frame.locals[slot] {
            Value::ScalarCell(cell) => Value::ScalarCell(cell.clone()),
            value => {
                let cell = Arc::new(Mutex::new(value.clone()));
                frame.locals[slot] = Value::ScalarCell(cell.clone());
                Value::ScalarCell(cell)
            }
        }
    }
    /// The child index and type at one relative word offset inside an inline
    /// aggregate. Arrays keep their length/tag word at offset zero; records
    /// start their fields at word one.
    fn place_child(&self, ty: Type, offset: usize) -> Option<(usize, Type)> {
        let id = ty.layout()?;
        if let Some((element, _)) = self.program.enums[id].array {
            let width = self.program.width(element);
            if offset < 1 || width == 0 || !(offset - 1).is_multiple_of(width) {
                return None;
            }
            return Some(((offset - 1) / width, element));
        }
        let variant = &self.program.enums[id].variants[0];
        let mut at = self.program.enums[id].tag_words();
        for (index, field) in variant.fields.iter().enumerate() {
            if at == offset {
                return Some((index, *field));
            }
            at += self.program.width(*field);
        }
        None
    }
    /// Navigate to the value at a checked place path for a field write.
    fn place_navigate_mut<'a>(
        &self,
        value: &'a mut Value,
        steps: &[(usize, Type)],
    ) -> Option<&'a mut Value> {
        if steps.is_empty() {
            return Some(value);
        }
        let (offset, container) = steps[0];
        let (index, _) = self.place_child(container, offset)?;
        let Value::Enum { fields, .. } = value else {
            return None;
        };
        let child = fields.get_mut(index)?;
        self.place_navigate_mut(child, &steps[1..])
    }
    /// Read the value at a checked place path from a snapshot of its root.
    fn place_read(&self, value: Value, steps: &[(usize, Type)]) -> Option<Value> {
        let mut current = value;
        for (offset, container) in steps {
            let (index, _) = self.place_child(*container, *offset)?;
            let Value::Enum { fields, .. } = current else {
                return None;
            };
            current = fields.get(index)?.clone();
        }
        Some(current)
    }
    /// Move the value at a checked place path out of a root snapshot.
    fn place_take(&self, value: &mut Value, steps: &[(usize, Type)]) -> Option<Value> {
        if steps.is_empty() {
            return Some(std::mem::replace(value, Value::Scalar(0)));
        }
        let (offset, container) = steps[0];
        let (index, _) = self.place_child(container, offset)?;
        let Value::Enum { fields, .. } = value else {
            return None;
        };
        let child = fields.get_mut(index)?;
        self.place_take(child, &steps[1..])
    }
    /// Store a replacement at a checked place path without dropping anything.
    fn place_store(&self, value: &mut Value, steps: &[(usize, Type)], replacement: Value) -> bool {
        if steps.is_empty() {
            *value = replacement;
            return true;
        }
        let (offset, container) = steps[0];
        let Some((index, _)) = self.place_child(container, offset) else {
            return false;
        };
        let Value::Enum { fields, .. } = value else {
            return false;
        };
        let Some(child) = fields.get_mut(index) else {
            return false;
        };
        self.place_store(child, &steps[1..], replacement)
    }
    /// Read a whole place through a checked reference value.
    fn reference_read(&self, reference: &Value, _pointee: Type) -> Option<Value> {
        match reference {
            Value::RecordRef(cell) => Some(cell.lock().unwrap().clone()),
            Value::PlaceRef { root, steps, .. } => {
                let value = root.lock().unwrap().clone();
                self.place_read(value, steps)
            }
            Value::ElementRef {
                owner,
                index,
                steps,
                ..
            } => {
                let element = self.element_value(*owner, *index)?;
                self.place_read(element, steps)
            }
            Value::SliceElementRef { view, index, steps } => {
                let element = self.slice_element(view, *index, Span::default()).ok()?;
                self.place_read(element, steps)
            }
            _ => None,
        }
    }
    /// Snapshot of one vector element.
    fn element_value(&self, owner: usize, index: usize) -> Option<Value> {
        let Value::Vector { items, .. } = self.heap.get(owner)? else {
            return None;
        };
        items.get(index).cloned()
    }
    /// Replace the value behind a checked reference, destroying the old affine
    /// payload exactly once. Linear referents are rejected by the checker.
    fn reference_replace(
        &mut self,
        reference: &Value,
        pointee: Type,
        replacement: Value,
    ) -> Result<()> {
        let old = self.reference_swap(reference, replacement)?;
        if self.program.owns(pointee) {
            self.drop_value(old)?;
        }
        Ok(())
    }
    /// Store `replacement` behind a checked reference and return the old
    /// value without dropping it. Callers that update part of the referent in
    /// place (a view over a referenced record field) write back the whole
    /// referent this way, so no owner is dropped or duplicated.
    fn reference_swap(&mut self, reference: &Value, replacement: Value) -> Result<Value> {
        Ok(match reference {
            Value::RecordRef(cell) => std::mem::replace(&mut *cell.lock().unwrap(), replacement),
            Value::SliceElementRef { view, index, steps } => {
                let mut element = self.slice_element(view, *index, Span::default())?;
                let old = self.place_take(&mut element, steps).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal error: element path is missing")
                })?;
                if !self.place_store(&mut element, steps, replacement) {
                    return Err(Diagnostic::new(
                        Span::default(),
                        "internal error: element replacement has no target",
                    ));
                }
                self.slice_set(view, *index, element, Span::default())?;
                old
            }
            Value::PlaceRef { root, steps, .. } => {
                let mut whole = root.lock().unwrap().clone();
                let old = self.place_take(&mut whole, steps).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal error: place path is missing")
                })?;
                if !self.place_store(&mut whole, steps, replacement) {
                    return Err(Diagnostic::new(
                        Span::default(),
                        "internal error: place replacement has no target",
                    ));
                }
                *root.lock().unwrap() = whole;
                old
            }
            Value::ElementRef {
                owner,
                index,
                steps,
                ..
            } => {
                let mut element = self.element_value(*owner, *index).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal error: vector element is missing")
                })?;
                let old = self.place_take(&mut element, steps).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal error: element path is missing")
                })?;
                if !self.place_store(&mut element, steps, replacement) {
                    return Err(Diagnostic::new(
                        Span::default(),
                        "internal error: element replacement has no target",
                    ));
                }
                let mut vector = self.heap.get(*owner).ok_or_else(|| {
                    Diagnostic::new(Span::default(), "internal error: vector owner is missing")
                })?;
                let Value::Vector { items, .. } = &mut vector else {
                    return Err(Diagnostic::new(
                        Span::default(),
                        "internal error: element reference owner is not a vector",
                    ));
                };
                items[*index] = element;
                self.heap.insert(*owner, vector);
                old
            }
            _ => {
                return Err(Diagnostic::new(
                    Span::default(),
                    "internal error: reference write has no writable place",
                ));
            }
        })
    }
    /// Store a temporary-owner initializer into its already-declared hidden
    /// slot. Re-initializing the same source occurrence (for example a loop
    /// condition) releases the previous value first, so repeated evaluation
    /// neither leaks nor double-drops it.
    ///
    /// Kept out of line so the large recursive expression frame stays bounded.
    #[inline(never)]
    fn store_initialized_owner(
        &mut self,
        slot: usize,
        value: Value,
        frame: &mut Frame,
    ) -> Result<()> {
        let id = self.program.functions[frame.function].local_resources[slot];
        self.drop_resource(id, frame)?;
        self.store_local(slot, value, frame);
        self.local_active(slot, frame);
        Ok(())
    }
    /// Resolve one local slot to its pinned storage cell, creating the cell on
    /// first use so every reference to an inline aggregate aliases one live
    /// location.
    fn resolve_local_place(&mut self, slot: usize, frame: &mut Frame) -> Result<ResolvedPlace> {
        let ty = self.program.functions[frame.function].locals[slot].ty;
        let current = frame.locals[slot].clone();
        let cell = match current {
            Value::RecordCell(cell) | Value::ArrayCell(cell) => cell,
            value => {
                let cell = Arc::new(Mutex::new(value));
                let array = ty
                    .layout()
                    .is_some_and(|id| self.program.enums[id].array.is_some());
                frame.locals[slot] = if array {
                    Value::ArrayCell(cell.clone())
                } else {
                    Value::RecordCell(cell.clone())
                };
                cell
            }
        };
        Ok(ResolvedPlace::Cell {
            root: cell,
            steps: Vec::new(),
            ty,
        })
    }
    /// Resolve a checked place expression into root storage plus a typed word
    /// path. Inline aggregates are pinned on first use so every reference to
    /// them aliases one live location.
    fn resolve_place(&mut self, place: &Expr, frame: &mut Frame) -> Result<PlaceFlow> {
        match &place.kind {
            ExprKind::Local(slot) | ExprKind::Peek(slot) | ExprKind::Move(slot) => {
                Ok(PlaceFlow::Place(self.resolve_local_place(*slot, frame)?))
            }
            ExprKind::InitOwner { slot, value: init } => {
                // A borrowed place rooted at a temporary owner. The
                // initializer may itself return, break, continue, or `?`
                // before the place exists, so propagate that flow exactly as
                // the un-hoisted expression would.
                let value = match self.expr(init, frame)? {
                    Flow::Value(value) => value,
                    flow => return Ok(flow.into()),
                };
                self.consume(init, frame);
                self.store_initialized_owner(*slot, value, frame)?;
                Ok(PlaceFlow::Place(self.resolve_local_place(*slot, frame)?))
            }
            ExprKind::Project(base, offset) => {
                if base.ty.is_ref() {
                    let reference = match self.expr(base, frame)? {
                        Flow::Value(value) => value,
                        flow => return Ok(flow.into()),
                    };
                    let resolved = self.resolve_reference_place(&reference, *offset, base.ty)?;
                    return Ok(PlaceFlow::Place(resolved));
                }
                let mut resolved = match self.resolve_place(base, frame)? {
                    PlaceFlow::Place(resolved) => resolved,
                    flow => return Ok(flow),
                };
                let (container, child) = match &resolved {
                    ResolvedPlace::Cell { ty, .. }
                    | ResolvedPlace::Element { ty, .. }
                    | ResolvedPlace::SliceElement { ty, .. } => {
                        let (_, child) = self.place_child(*ty, *offset).ok_or_else(|| {
                            Diagnostic::new(place.span, "internal error: place offset has no field")
                        })?;
                        (*ty, child)
                    }
                };
                match &mut resolved {
                    ResolvedPlace::Cell { steps, ty, .. }
                    | ResolvedPlace::Element { steps, ty, .. }
                    | ResolvedPlace::SliceElement { steps, ty, .. } => {
                        steps.push((*offset, container));
                        *ty = child;
                    }
                }
                Ok(PlaceFlow::Place(resolved))
            }
            ExprKind::PlaceIndex { base, index, .. } if base.ty.is_slice() => {
                // One element of a slice view: the view is evaluated (not
                // moved), then the index is checked against its length. A
                // byte-backed view has no word-sized element to address.
                let view = match self.expr(base, frame)? {
                    Flow::Value(value) => value,
                    flow => return Ok(flow.into()),
                };
                let index = match self.expr(index, frame)? {
                    Flow::Value(value) => value.scalar(),
                    flow => return Ok(flow.into()),
                };
                let length = self.slice_len(&view, place.span)?;
                let Some(index) = usize::try_from(index).ok().filter(|index| *index < length)
                else {
                    return Err(Diagnostic::new(
                        place.span,
                        "panic: slice index out of bounds",
                    ));
                };
                if let Value::Slice(inner) = &view
                    && inner.array.is_none()
                    && let Value::Borrowed(id) | Value::Owned(id) = inner.base.as_ref()
                    && matches!(self.heap.get(*id), Some(Value::Buffer { .. }))
                {
                    return Err(Diagnostic::new(
                        place.span,
                        "panic: a byte-backed slice element has no word-sized address",
                    ));
                }
                let element = self.program.pointees[base.ty.slice_element().expect("slice")];
                Ok(PlaceFlow::Place(ResolvedPlace::SliceElement {
                    view: Box::new(view),
                    index,
                    steps: Vec::new(),
                    ty: element,
                }))
            }
            ExprKind::PlaceIndex { base, index, .. } => {
                // Resolve the base before evaluating the index, matching checking.
                let (base_value, base_place) = if matches!(base.ty, Type::Vec(_)) {
                    let value = match self.expr(base, frame)? {
                        Flow::Value(value) => value,
                        flow => return Ok(flow.into()),
                    };
                    (Some(value), None)
                } else {
                    let place = match self.resolve_place(base, frame)? {
                        PlaceFlow::Place(place) => place,
                        flow => return Ok(flow),
                    };
                    (None, Some(place))
                };
                let index = match self.expr(index, frame)? {
                    Flow::Value(value) => value.scalar(),
                    flow => return Ok(flow.into()),
                };
                if index < 0 {
                    return Err(Diagnostic::new(place.span, "panic: index out of bounds"));
                }
                let index = index as usize;
                if let Type::Vec(_) = base.ty {
                    let Some(Value::Owned(owner)) = base_value else {
                        return Err(Diagnostic::new(
                            place.span,
                            "internal error: checked vector place has no owned handle",
                        ));
                    };
                    let Some(Value::Vector { items, .. }) = self.heap.get(owner) else {
                        return Err(Diagnostic::new(
                            place.span,
                            "internal ownership error: dangling vector place",
                        ));
                    };
                    let element = match base.ty {
                        Type::Vec(pointer) => self.program.pointees[pointer],
                        _ => unreachable!(),
                    };
                    if index >= items.len() {
                        return Err(Diagnostic::new(place.span, "panic: index out of bounds"));
                    }
                    return Ok(PlaceFlow::Place(ResolvedPlace::Element {
                        owner,
                        index,
                        steps: Vec::new(),
                        ty: element,
                    }));
                }
                let (element, length) = base
                    .ty
                    .layout()
                    .and_then(|id| self.program.enums[id].array)
                    .ok_or_else(|| {
                        Diagnostic::new(
                            place.span,
                            "internal error: index place has no array or vector storage",
                        )
                    })?;
                if index >= length {
                    return Err(Diagnostic::new(place.span, "panic: index out of bounds"));
                }
                let mut resolved = base_place.expect("checked array place");
                let container = base.ty;
                let offset = 1 + index * self.program.width(element);
                match &mut resolved {
                    ResolvedPlace::Cell { steps, ty, .. }
                    | ResolvedPlace::Element { steps, ty, .. }
                    | ResolvedPlace::SliceElement { steps, ty, .. } => {
                        steps.push((offset, container));
                        *ty = element;
                    }
                }
                Ok(PlaceFlow::Place(resolved))
            }
            _ => Err(Diagnostic::new(
                place.span,
                "internal error: expression is not an addressable place",
            )),
        }
    }
    fn resolve_reference_place(
        &mut self,
        reference: &Value,
        offset: usize,
        reference_ty: Type,
    ) -> Result<ResolvedPlace> {
        let pointer = reference_ty.ref_pointee().ok_or_else(|| {
            Diagnostic::new(
                Span::default(),
                "internal error: place base is not a reference",
            )
        })?;
        let pointee = self.program.pointees[pointer];
        let (_, child) = self.place_child(pointee, offset).ok_or_else(|| {
            Diagnostic::new(
                Span::default(),
                "internal error: reference field place has no field",
            )
        })?;
        match reference {
            Value::RecordRef(root) => Ok(ResolvedPlace::Cell {
                root: root.clone(),
                steps: vec![(offset, pointee)],
                ty: child,
            }),
            Value::PlaceRef { root, steps, .. } => {
                let mut steps = steps.clone();
                steps.push((offset, pointee));
                Ok(ResolvedPlace::Cell {
                    root: root.clone(),
                    steps,
                    ty: child,
                })
            }
            Value::SliceElementRef { view, index, steps } => {
                let mut steps = steps.clone();
                steps.push((offset, pointee));
                Ok(ResolvedPlace::SliceElement {
                    view: view.clone(),
                    index: *index,
                    steps,
                    ty: child,
                })
            }
            Value::ElementRef {
                owner,
                index,
                steps,
                ..
            } => {
                let mut steps = steps.clone();
                steps.push((offset, pointee));
                Ok(ResolvedPlace::Element {
                    owner: *owner,
                    index: *index,
                    steps,
                    ty: child,
                })
            }
            _ => Err(Diagnostic::new(
                Span::default(),
                "internal error: reference place has no storage root",
            )),
        }
    }
    /// Borrow one direct local binding. Inline aggregates are promoted to a
    /// shared cell so later reads and writes through the reference observe the
    /// live storage rather than a snapshot.
    #[inline(never)]
    fn borrow_local_value(&mut self, slot: usize, frame: &mut Frame) -> Result<Value> {
        let ty = self.program.functions[frame.function].locals[slot].ty;
        let owner_like = matches!(
            ty,
            Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::AllocatorContext
                | Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::Task(_)
        );
        if !owner_like {
            // Any addressable inline value (record, array, scalar, or enum) is
            // pinned to shared storage so `&x`, `&mut x`, and field/index
            // references can alias the live location.
            let current = frame.locals[slot].clone();
            let cell = match current {
                Value::RecordCell(cell) | Value::ArrayCell(cell) => cell,
                value => {
                    let cell = Arc::new(Mutex::new(value));
                    let array = ty
                        .layout()
                        .is_some_and(|id| self.program.enums[id].array.is_some());
                    frame.locals[slot] = if array {
                        Value::ArrayCell(cell.clone())
                    } else {
                        Value::RecordCell(cell.clone())
                    };
                    cell
                }
            };
            // The local's ownership resource must alias the pinned cell now,
            // so a later replacement through the reference is dropped from the
            // live contents rather than a stale snapshot taken at binding time.
            self.local_active(slot, frame);
            Ok(Value::RecordRef(cell))
        } else {
            match frame.locals[slot].clone() {
                Value::Owned(id) => Ok(Value::Borrowed(id)),
                Value::Task(id) => Ok(Value::TaskRef(id)),
                Value::Arena { state } => Ok(Value::ArenaRef(state)),
                Value::ArenaBox { state, slot } => Ok(Value::ArenaBoxRef { state, slot }),
                Value::AllocatorContext(state) => Ok(Value::AllocatorContextRef(state)),
                _ => unreachable!("checked borrow of an owned handle"),
            }
        }
    }
    /// Convert a resolved place into its one-word checked reference value.
    fn borrow_place(&mut self, place: &Expr, frame: &mut Frame) -> Result<PlaceFlow> {
        if matches!(
            place.ty,
            Type::Box(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::AllocBox(_)
                | Type::AllocVec(_)
                | Type::AllocatorContext
                | Type::Arena
                | Type::ArenaBox(_)
        ) {
            let value = match self.expr(place, frame)? {
                Flow::Value(value) => value,
                flow => return Ok(flow.into()),
            };
            return match value {
                Value::Owned(id) => Ok(PlaceFlow::Value(Value::Borrowed(id))),
                Value::AllocatorContext(state) => {
                    Ok(PlaceFlow::Value(Value::AllocatorContextRef(state)))
                }
                Value::Arena { state } => Ok(PlaceFlow::Value(Value::ArenaRef(state))),
                Value::ArenaBox { state, slot } => {
                    Ok(PlaceFlow::Value(Value::ArenaBoxRef { state, slot }))
                }
                _ => Err(Diagnostic::new(
                    place.span,
                    "internal error: owning field reference has no owned handle",
                )),
            };
        }
        let resolved = match self.resolve_place(place, frame)? {
            PlaceFlow::Place(resolved) => resolved,
            flow => return Ok(flow),
        };
        Ok(PlaceFlow::Value(match resolved {
            ResolvedPlace::Cell { root, steps, .. } => Value::PlaceRef { root, steps },
            ResolvedPlace::SliceElement {
                view, index, steps, ..
            } => Value::SliceElementRef { view, index, steps },
            ResolvedPlace::Element {
                owner,
                index,
                steps,
                ..
            } => Value::ElementRef {
                owner,
                index,
                steps,
            },
        }))
    }
    /// One vector element reference used by explicit `PlaceIndex` evaluation
    /// (only produced as a borrow operand).
    fn place_index_reference(&mut self, place: &Expr, frame: &mut Frame) -> Result<PlaceFlow> {
        let ExprKind::PlaceIndex { base, index, .. } = &place.kind else {
            return Err(Diagnostic::new(
                place.span,
                "internal error: expected a place index",
            ));
        };
        let index = match self.expr(index, frame)? {
            Flow::Value(value) => value.scalar(),
            flow => return Ok(flow.into()),
        };
        if matches!(base.ty, Type::Vec(_)) {
            let base_value = match self.expr(base, frame)? {
                Flow::Value(value) => value,
                flow => return Ok(flow.into()),
            };
            let Value::Owned(owner) = base_value else {
                return Err(Diagnostic::new(
                    place.span,
                    "internal error: checked vector place has no owned handle",
                ));
            };
            let Some(Value::Vector { items, .. }) = self.heap.get(owner) else {
                return Err(Diagnostic::new(
                    place.span,
                    "internal ownership error: dangling vector place",
                ));
            };
            if index < 0 || index as usize >= items.len() {
                return Err(Diagnostic::new(place.span, "panic: index out of bounds"));
            }
            return Ok(PlaceFlow::Value(Value::ElementRef {
                owner,
                index: index as usize,
                steps: Vec::new(),
            }));
        }
        let resolved = match self.resolve_place(place, frame)? {
            PlaceFlow::Place(resolved) => resolved,
            flow => return Ok(flow),
        };
        Ok(PlaceFlow::Value(match resolved {
            ResolvedPlace::Cell { root, steps, .. } => Value::PlaceRef { root, steps },
            ResolvedPlace::SliceElement {
                view, index, steps, ..
            } => Value::SliceElementRef { view, index, steps },
            ResolvedPlace::Element {
                owner,
                index,
                steps,
                ..
            } => Value::ElementRef {
                owner,
                index,
                steps,
            },
        }))
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
        let Value::Slice(view) = value else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a &str view",
            ));
        };
        let SliceValue {
            base, start, len, ..
        } = &**view;
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
            Value::Slice(_) => self.str_data(value, span),
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
            StrOp::AsciiUpper | StrOp::AsciiLower => {
                let mut data = data;
                if op == StrOp::AsciiUpper {
                    data.make_ascii_uppercase();
                } else {
                    data.make_ascii_lowercase();
                }
                self.write_str_data(&args[0], &data, span)?;
                Ok(Value::Scalar(0))
            }
            StrOp::SetScalar => {
                let index = usize::try_from(args[1].scalar())
                    .ok()
                    .filter(|index| *index < data.len() && (data[*index] & 0xC0) != 0x80);
                let Some(index) = index else {
                    return Err(Diagnostic::new(
                        span,
                        "panic: Str.set_scalar offset is not a scalar boundary inside the view",
                    ));
                };
                let scalar = u32::try_from(args[2].scalar())
                    .ok()
                    .and_then(char::from_u32)
                    .ok_or_else(|| Diagnostic::new(span, "internal error: invalid Char"))?;
                let old = std::str::from_utf8(&data[index..])
                    .ok()
                    .and_then(|text| text.chars().next())
                    .ok_or_else(|| Diagnostic::new(span, "internal error: invalid text view"))?;
                if old.len_utf8() != scalar.len_utf8() {
                    return Err(Diagnostic::new(
                        span,
                        "panic: Str.set_scalar needs a scalar with the same UTF-8 width as the one it replaces",
                    ));
                }
                let mut data = data;
                scalar.encode_utf8(&mut data[index..index + scalar.len_utf8()]);
                self.write_str_data(&args[0], &data, span)?;
                Ok(Value::Scalar(0))
            }
        }
    }
    /// Store `bytes` back over the range an exclusive text view covers. The
    /// caller keeps the length, so the owner's buffer never grows or shrinks.
    fn write_str_data(&mut self, value: &Value, bytes: &[u8], span: Span) -> Result<()> {
        let Value::Slice(view) = value else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a &mut str view",
            ));
        };
        let SliceValue {
            base, start, len, ..
        } = &**view;
        let Value::Borrowed(id) = base.as_ref() else {
            return Err(Diagnostic::new(
                span,
                "internal error: invalid &mut str view backing storage",
            ));
        };
        let Some(Value::Buffer { mut data, capacity }) = self.heap.get(*id) else {
            return Err(Diagnostic::new(
                span,
                "internal ownership error: dangling text view",
            ));
        };
        if bytes.len() != *len || data.len() < start + len {
            return Err(Diagnostic::new(
                span,
                "internal error: text write changed the length",
            ));
        }
        data[*start..start + len].copy_from_slice(bytes);
        self.heap.insert(*id, Value::Buffer { data, capacity });
        Ok(())
    }
    /// Evaluate one slice construction. Kept out of the recursive expression
    /// match so the evaluator's frame stays small enough for deep user
    /// recursion (the JSON limit tests exercise that headroom).
    #[inline(never)]
    #[allow(clippy::too_many_arguments)]
    fn eval_slice(
        &mut self,
        expr: &Expr,
        base: &Expr,
        start: &Option<Box<Expr>>,
        end: &Option<Box<Expr>>,
        check: bool,
        text: bool,
        field: &Option<Vec<usize>>,
        frame: &mut Frame,
    ) -> Result<Flow> {
        let mut reference = None;
        let array = if field.is_some() {
            let slot = projection_root_slot(base).ok_or_else(|| {
                Diagnostic::new(expr.span, "internal error: field view has no record root")
            })?;
            // A temporary record root is initialized at the view's source
            // position; its hidden owner then pins it like a local.
            if let Some((slot, init)) = projection_root_init(base) {
                let value = value!(self.expr(init, frame));
                self.consume(init, frame);
                self.store_initialized_owner(slot, value, frame)?;
            }
            let current = frame.locals[slot].clone();
            let root_ty = self.program.functions[frame.function].locals[slot].ty;
            if root_ty.is_ref() {
                reference = Some(Box::new(current.clone()));
            }
            let cell = match current {
                _ if root_ty.is_ref() => Arc::new(Mutex::new(Value::Scalar(0))),
                Value::RecordCell(cell) => cell,
                value => {
                    let cell = Arc::new(Mutex::new(value));
                    frame.locals[slot] = Value::RecordCell(cell.clone());
                    cell
                }
            };
            reference.is_none().then_some(cell)
        } else {
            match &base.kind {
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
                // A shared DynArray view aliases the pinned record cell, so
                // later reads see the same live inline storage. The
                // ownership pass rejects push/pop/assignment while the view
                // is live, so this shared cell is never mutated behind it.
                ExprKind::Borrow(slot)
                    if self.program.functions[frame.function].locals[*slot]
                        .ty
                        .layout()
                        .is_some_and(|id| self.program.enums[id].dynamic_array.is_some()) =>
                {
                    let current = frame.locals[*slot].clone();
                    let cell = match current {
                        Value::RecordCell(cell) => cell,
                        value => {
                            let cell = Arc::new(Mutex::new(value));
                            frame.locals[*slot] = Value::RecordCell(cell.clone());
                            cell
                        }
                    };
                    Some(cell)
                }
                _ => None,
            }
        };
        let base_value = match (&array, field) {
            (None, Some(path)) if reference.is_some() => {
                let referent = self
                    .reference_read(reference.as_ref().unwrap(), Type::Unit)
                    .ok_or_else(|| {
                        Diagnostic::new(expr.span, "internal error: dangling field view reference")
                    })?;
                navigate_field(&referent, path).cloned().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "internal error: DynArray field view has no array field",
                    )
                })?
            }
            (Some(cell), Some(path)) => {
                let value = cell.lock().unwrap().clone();
                navigate_field(&value, path).cloned().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "internal error: DynArray field view has no array field",
                    )
                })?
            }
            (Some(cell), None) => cell.lock().unwrap().clone(),
            (None, _) => value!(self.expr(base, frame)),
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
        if check && (start > end || end > base_len) {
            return Err(Diagnostic::new(
                expr.span,
                "panic: slice range out of bounds",
            ));
        }
        if text && check {
            let bytes = self.text_base_bytes(&base_value, expr.span)?;
            let boundary = |index: usize| index == bytes.len() || bytes[index] & 0xC0 != 0x80;
            if !boundary(start) || !boundary(end) {
                return Err(Diagnostic::new(
                    expr.span,
                    "panic: text range is not on Unicode scalar boundaries",
                ));
            }
        }
        Ok(Flow::Value(match base_value {
            Value::Slice(prior) => Value::Slice(Box::new(SliceValue {
                base: prior.base,
                start: prior.start + start,
                len: end - start,
                array: array.or(prior.array),
                field: field.clone().or(prior.field),
                reference: reference.or(prior.reference),
            })),
            base => Value::Slice(Box::new(SliceValue {
                base: Box::new(base),
                start,
                len: end - start,
                array,
                field: field.clone(),
                reference,
            })),
        }))
    }

    fn slice_len(&self, value: &Value, span: Span) -> Result<usize> {
        match value {
            Value::Slice(view) => Ok(view.len),
            Value::Enum { fields, .. } => Ok(fields.len()),
            Value::DynArray { items, .. } => Ok(items.len()),
            Value::RecordRef(cell) => match &*cell.lock().unwrap() {
                Value::DynArray { items, .. } => Ok(items.len()),
                Value::Enum { fields, .. } => Ok(fields.len()),
                _ => Err(Diagnostic::new(
                    span,
                    "internal error: invalid record slice source",
                )),
            },
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
        let Value::Slice(view) = view else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a slice view",
            ));
        };
        let SliceValue {
            base,
            start,
            len,
            array,
            field,
            reference,
        } = &**view;
        if index >= *len {
            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
        }
        let position = start + index;
        if let (Some(reference), Some(path)) = (reference, field) {
            let referent = self.reference_read(reference, Type::Unit).ok_or_else(|| {
                Diagnostic::new(span, "internal error: dangling field view reference")
            })?;
            let Some(Value::DynArray { items, .. }) = navigate_field(&referent, path) else {
                return Err(Diagnostic::new(
                    span,
                    "internal error: slice DynArray field is missing",
                ));
            };
            return items.get(position).cloned().ok_or_else(|| {
                Diagnostic::new(span, "internal error: slice array index out of bounds")
            });
        }
        if let Some(cell) = array {
            let value = cell.lock().unwrap();
            let value = match field {
                Some(path) => navigate_field(&value, path).ok_or_else(|| {
                    Diagnostic::new(span, "internal error: slice DynArray field is missing")
                })?,
                None => &*value,
            };
            return match value {
                Value::Enum { fields, .. } => fields.get(position).cloned().ok_or_else(|| {
                    Diagnostic::new(span, "internal error: slice array index out of bounds")
                }),
                Value::DynArray { items, .. } => items.get(position).cloned().ok_or_else(|| {
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
        let Value::Slice(view) = view else {
            return Err(Diagnostic::new(
                span,
                "internal error: expected a slice view",
            ));
        };
        let SliceValue {
            base,
            start,
            len,
            array,
            field,
            reference,
        } = &**view;
        if index >= *len {
            return Err(Diagnostic::new(span, "panic: slice index out of bounds"));
        }
        let position = start + index;
        if let (Some(reference), Some(path)) = (reference, field) {
            let mut referent = self.reference_read(reference, Type::Unit).ok_or_else(|| {
                Diagnostic::new(span, "internal error: dangling field view reference")
            })?;
            let Some(Value::DynArray { items, .. }) = navigate_field_mut(&mut referent, path)
            else {
                return Err(Diagnostic::new(
                    span,
                    "internal error: slice DynArray field is missing",
                ));
            };
            let Some(slot) = items.get_mut(position) else {
                return Err(Diagnostic::new(
                    span,
                    "internal error: slice array index out of bounds",
                ));
            };
            // Copyable elements only: the old slot owns nothing.
            *slot = value;
            let reference = reference.clone();
            self.reference_swap(&reference, referent)?;
            return Ok(());
        }
        if let Some(cell) = array {
            let mut cell = cell.lock().unwrap();
            let cell = match field {
                Some(path) => navigate_field_mut(&mut cell, path).ok_or_else(|| {
                    Diagnostic::new(span, "internal error: slice DynArray field is missing")
                })?,
                None => &mut *cell,
            };
            return match cell {
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
                Value::DynArray { items, .. } => {
                    let Some(slot) = items.get_mut(position) else {
                        return Err(Diagnostic::new(
                            span,
                            "internal error: slice DynArray index out of bounds",
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
    /// Compare two structural record values field by field. The checker has
    /// already restricted the row to comparable scalar leaves and nested
    /// structural rows, so every compared value is a copyable scalar.
    fn struct_value_eq(&self, ty: Type, left: &Value, right: &Value, span: Span) -> Result<bool> {
        let (
            Value::Enum {
                fields: left_fields,
                ..
            },
            Value::Enum {
                fields: right_fields,
                ..
            },
        ) = (left, right)
        else {
            return Err(Diagnostic::new(
                span,
                "internal error: structural equality received a non-record value",
            ));
        };
        let layout = ty
            .layout()
            .filter(|id| self.program.enums[*id].structural)
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    "internal error: structural equality type is not a structural row",
                )
            })?;
        let types = &self.program.enums[layout].variants[0].fields;
        if left_fields.len() != types.len() || right_fields.len() != types.len() {
            return Err(Diagnostic::new(
                span,
                "internal error: structural equality field count disagrees with its row",
            ));
        }
        for ((left, right), field) in left_fields.iter().zip(right_fields).zip(types) {
            let equal = if field.layout().is_some() {
                self.struct_value_eq(*field, left, right, span)?
            } else {
                left.scalar() == right.scalar()
            };
            if !equal {
                return Ok(false);
            }
        }
        Ok(true)
    }
    fn apply_struct_coercion(
        &mut self,
        value: Value,
        kept: &[(usize, usize, Option<Coercion>)],
        drops: &[(usize, Type)],
        span: Span,
    ) -> Result<Value> {
        let Value::Enum { fields, .. } = value else {
            return Err(Diagnostic::new(
                span,
                "internal error: structural record conversion received a non-record value",
            ));
        };
        let mut source = fields.into_iter().map(Some).collect::<Vec<_>>();
        let mut target = Vec::with_capacity(kept.len());
        for (_, source_index, coercion) in kept {
            let Some(field) = source.get_mut(*source_index).and_then(|field| field.take()) else {
                return Err(Diagnostic::new(
                    span,
                    "internal error: structural conversion reuses a source field",
                ));
            };
            target.push(match coercion {
                Some(coercion) => self.apply_nested_coercion(field, coercion, span)?,
                None => field,
            });
        }
        for (source_index, _) in drops {
            if let Some(field) = source.get_mut(*source_index).and_then(|field| field.take()) {
                self.drop_value(field)?;
            }
        }
        Ok(Value::Enum {
            tag: 0,
            fields: target,
        })
    }
    fn apply_nested_coercion(
        &mut self,
        value: Value,
        coercion: &Coercion,
        span: Span,
    ) -> Result<Value> {
        match coercion {
            Coercion::Inject { tag } => Ok(Value::Union {
                tag: *tag,
                value: Box::new(value),
            }),
            Coercion::Repack { map } => {
                let Value::Union { tag, value } = value else {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: nested union repacking received a non-union value",
                    ));
                };
                let Some(target) = map.get(tag) else {
                    return Err(Diagnostic::new(
                        span,
                        "internal error: nested union repacking has no alternative mapping",
                    ));
                };
                Ok(Value::Union {
                    tag: *target,
                    value,
                })
            }
            Coercion::Struct { kept, drops, .. } => {
                self.apply_struct_coercion(value, kept, drops, span)
            }
            Coercion::DynBox { member, .. } => {
                self.stats.allocation();
                Ok(Value::DynObject {
                    member: *member,
                    value: Arc::new(Mutex::new(value)),
                })
            }
            Coercion::DynUpcast { from, to } => self.dyn_upcast(*from, *to, value, span),
            Coercion::Callable {
                function, capture, ..
            } => {
                if capture.is_some() {
                    let environment = self.allocate(Value::Closure {
                        captures: vec![value],
                    });
                    let Value::Owned(environment) = environment else {
                        unreachable!("closure environment allocation")
                    };
                    Ok(Value::Function {
                        function: *function,
                        environment: Some(environment),
                    })
                } else {
                    Ok(Value::Function {
                        function: *function,
                        environment: None,
                    })
                }
            }
        }
    }
    fn dyn_array_call(
        &mut self,
        op: DynArrayOp,
        element: Type,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value> {
        // Any checked reference may point at the array: a pinned local, a
        // record field place, a vector element, or a slice element.
        let borrowed = match &args[0] {
            Value::RecordRef(cell) => cell.lock().unwrap().clone(),
            other => self.reference_read(other, Type::Unit).ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "internal error: DynArray operation expected a borrow, found {other:?}"
                    ),
                )
            })?,
        };
        let Value::DynArray { items, .. } = &borrowed else {
            return Err(Diagnostic::new(
                span,
                "internal error: DynArray borrow does not point at a runtime-sized array",
            ));
        };
        match op {
            DynArrayOp::Len => Ok(Value::Scalar(items.len() as i64)),
            DynArrayOp::Get => {
                let index = usize::try_from(args[1].scalar())
                    .map_err(|_| Diagnostic::new(span, "panic: DynArray index out of bounds"))?;
                let Some(value) = items.get(index) else {
                    return Err(Diagnostic::new(span, "panic: DynArray index out of bounds"));
                };
                debug_assert!(!self.program.owns(element));
                Ok(value.clone())
            }
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
    /// Checked allocator-backed vector operations. Element storage always
    /// comes from the allocator recorded in the vector itself; growth allocates
    /// one fresh block and releases the previous block through the same pair,
    /// so every allocation is released exactly once by its own allocator.
    fn alloc_vec_call(
        &mut self,
        op: AllocVecOp,
        element: Type,
        mut args: Vec<Value>,
        result: Type,
        span: Span,
    ) -> Result<Value> {
        let failure = |message: &str| Diagnostic::new(span, message.to_owned());
        let width = self.program.width(element);
        let index_of = |value: &Value, len: usize| {
            usize::try_from(value.scalar())
                .ok()
                .filter(|i| *i < len)
                .ok_or_else(|| failure("panic: AllocVec index out of bounds"))
        };
        match op {
            AllocVecOp::Len | AllocVecOp::Get => {
                let Value::Borrowed(id) = args[0] else {
                    unreachable!("checked AllocVec borrow")
                };
                let Some(Value::AllocVector(state)) = self.heap.get(id) else {
                    return Err(failure(
                        "internal ownership error: dangling AllocVec borrow",
                    ));
                };
                if op == AllocVecOp::Len {
                    return Ok(Value::Scalar(state.items.len() as i64));
                }
                Ok(state.items[index_of(&args[1], state.items.len())?].clone())
            }
            AllocVecOp::Push | AllocVecOp::TryPush | AllocVecOp::Set => {
                let Value::Owned(id) = args.remove(0) else {
                    unreachable!("checked owned AllocVec")
                };
                let (index, value) = if op == AllocVecOp::Set {
                    (Some(args.remove(0)), args.remove(0))
                } else {
                    (None, args.remove(0))
                };
                let Some(Value::AllocVector(state)) = self.heap.take(id) else {
                    return Err(failure("internal ownership error: moved AllocVec"));
                };
                let AllocVectorState {
                    mut items,
                    mut capacity,
                    allocator,
                    mut block,
                } = *state;
                if let Some(index) = index {
                    let index = index_of(&index, items.len())?;
                    let old = std::mem::replace(&mut items[index], value);
                    self.heap.insert(
                        id,
                        Value::AllocVector(Box::new(AllocVectorState {
                            items,
                            capacity,
                            allocator,
                            block,
                        })),
                    );
                    self.drop_value(old)?;
                    return Ok(Value::Owned(id));
                }
                if items.len() == capacity {
                    let next = if capacity == 0 {
                        4
                    } else {
                        capacity.saturating_mul(2)
                    };
                    let bytes = next
                        .checked_mul(width)
                        .and_then(|words| words.checked_mul(8))
                        .ok_or_else(|| failure("panic: AllocVec capacity overflow"))?;
                    // A fallible append always uses the fresh-block path so a
                    // refusal can leave the vector untouched. The infallible
                    // path uses the recorded growth hook when one exists.
                    let can_grow = match &allocator {
                        AllocatorBinding::Static { realloc, .. } => {
                            realloc.is_some() && block.is_some()
                        }
                        AllocatorBinding::Context(_) => block.is_some(),
                    };
                    let fresh = if op == AllocVecOp::TryPush {
                        self.allocator_block(&allocator, bytes, span)?
                    } else if can_grow {
                        let old = block.take().expect("checked existing block");
                        let old_bytes = items.len() * width * 8;
                        let grown =
                            self.allocator_realloc_block(&allocator, old, old_bytes, bytes, span)?;
                        Some(grown)
                    } else {
                        self.allocator_block(&allocator, bytes, span)?
                    };
                    let Some(fresh) = fresh else {
                        if op == AllocVecOp::TryPush {
                            // Refusal: the vector keeps its elements, length,
                            // capacity, and block; the element comes back.
                            self.heap.insert(
                                id,
                                Value::AllocVector(Box::new(AllocVectorState {
                                    items,
                                    capacity,
                                    allocator,
                                    block,
                                })),
                            );
                            let unchanged = Value::Owned(id);
                            let shape = result
                                .layout()
                                .and_then(|id| self.program.enums[id].result)
                                .ok_or_else(|| {
                                    failure(
                                        "internal error: AllocVec.try_push result is not Result",
                                    )
                                })?;
                            return Ok(Value::Enum {
                                tag: shape.err_tag,
                                fields: vec![Value::Enum {
                                    tag: 0,
                                    fields: vec![unchanged, value],
                                }],
                            });
                        }
                        return Err(failure(&format!(
                            "panic: allocator refused a {bytes}-byte block"
                        )));
                    };
                    if let Some(old) = block.take() {
                        self.allocator_release(&allocator, old, span)?;
                    }
                    block = Some(fresh);
                    capacity = next;
                    self.stats.growth();
                }
                items.push(value);
                self.heap.insert(
                    id,
                    Value::AllocVector(Box::new(AllocVectorState {
                        items,
                        capacity,
                        allocator,
                        block,
                    })),
                );
                if op == AllocVecOp::TryPush {
                    let shape = result
                        .layout()
                        .and_then(|id| self.program.enums[id].result)
                        .ok_or_else(|| {
                            failure("internal error: AllocVec.try_push result is not Result")
                        })?;
                    return Ok(Value::Enum {
                        tag: shape.ok_tag,
                        fields: vec![Value::Owned(id)],
                    });
                }
                Ok(Value::Owned(id))
            }
            AllocVecOp::Pop => {
                let Value::Owned(id) = args.remove(0) else {
                    unreachable!("checked owned AllocVec")
                };
                let Some(Value::AllocVector(state)) = self.heap.take(id) else {
                    return Err(failure("internal ownership error: moved AllocVec"));
                };
                let AllocVectorState {
                    mut items,
                    capacity,
                    allocator,
                    block,
                } = *state;
                let Some(item) = items.pop() else {
                    return Err(failure("panic: AllocVec is empty"));
                };
                self.heap.insert(
                    id,
                    Value::AllocVector(Box::new(AllocVectorState {
                        items,
                        capacity,
                        allocator,
                        block,
                    })),
                );
                Ok(Value::Enum {
                    tag: 0,
                    fields: vec![Value::Owned(id), item],
                })
            }
            AllocVecOp::Clear => {
                let Value::Owned(id) = args.remove(0) else {
                    unreachable!("checked owned AllocVec")
                };
                let Some(Value::AllocVector(state)) = self.heap.take(id) else {
                    return Err(failure("internal ownership error: moved AllocVec"));
                };
                let AllocVectorState {
                    mut items,
                    capacity,
                    allocator,
                    block,
                } = *state;
                while let Some(item) = items.pop() {
                    self.drop_value(item)?;
                }
                self.heap.insert(
                    id,
                    Value::AllocVector(Box::new(AllocVectorState {
                        items,
                        capacity,
                        allocator,
                        block,
                    })),
                );
                Ok(Value::Owned(id))
            }
        }
    }
    fn vec_call(
        &mut self,
        op: VecOp,
        element: Type,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value> {
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
                    usable: box_allocation_capacity(
                        16 + capacity * self.program.width(element) * 8,
                    ),
                }))
            }
            VecOp::ClearBorrowed => {
                let Value::Borrowed(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Vector {
                    mut items,
                    capacity,
                    usable,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: borrowed vector"));
                };
                while let Some(item) = items.pop() {
                    self.drop_value(item)?;
                }
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Scalar(0))
            }
            VecOp::ReserveBorrowed => {
                let Value::Borrowed(id) = args[0] else {
                    unreachable!()
                };
                let additional = usize::try_from(args[1].scalar())
                    .map_err(|_| failure("panic: negative vector reserve"))?;
                let Some(Value::Vector {
                    items,
                    capacity,
                    mut usable,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: borrowed vector"));
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
                if needed > capacity {
                    capacity = needed;
                    let requested = 16 + capacity * self.program.width(element) * 8;
                    if requested > usable {
                        usable = box_allocation_capacity(requested);
                    }
                    self.stats.growth();
                }
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Scalar(0))
            }
            VecOp::Clear => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Vector {
                    mut items,
                    capacity,
                    usable,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                // Dropping from the end releases elements in reverse order
                // exactly once. The allocation and its capacity are retained.
                while let Some(item) = items.pop() {
                    self.drop_value(item)?;
                }
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Owned(id))
            }
            VecOp::Reserve => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let additional = usize::try_from(args[1].scalar())
                    .map_err(|_| failure("panic: negative vector reserve"))?;
                let Some(Value::Vector {
                    items,
                    capacity,
                    mut usable,
                }) = self.heap.take(id)
                else {
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
                    let requested = 16 + capacity * self.program.width(element) * 8;
                    if requested > usable {
                        usable = box_allocation_capacity(requested);
                    }
                    self.stats.growth();
                }
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Owned(id))
            }
            VecOp::TryReserve { ok_tag, err_tag } => {
                let Value::Owned(id) = args[0] else {
                    unreachable!()
                };
                let Some(Value::Vector {
                    items,
                    capacity,
                    usable,
                }) = self.heap.get(id)
                else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                let request = usize::try_from(args[1].scalar())
                    .ok()
                    .and_then(|additional| items.len().checked_add(additional))
                    .filter(|needed| *needed <= LIMIT)
                    .and_then(|needed| {
                        needed
                            .checked_mul(self.program.width(element) * 8)
                            .and_then(|bytes| bytes.checked_add(16))
                            .filter(|bytes| *bytes <= i64::MAX as usize)
                            .map(|bytes| (needed, bytes))
                    });
                let success = request.is_some_and(|(needed, bytes)| {
                    needed <= capacity || bytes <= usable || self.try_charge()
                });
                if success {
                    let (needed, bytes) = request.unwrap();
                    if needed > capacity {
                        self.heap.insert(
                            id,
                            Value::Vector {
                                items,
                                capacity: needed,
                                usable: usable.max(bytes),
                            },
                        );
                        self.stats.growth();
                    }
                }
                Ok(Value::Enum {
                    tag: if success { ok_tag } else { err_tag },
                    fields: vec![Value::Owned(id)],
                })
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
            VecOp::PushBorrowed | VecOp::SetBorrowed => {
                let Value::Borrowed(id) = args[0] else {
                    unreachable!()
                };
                let mut args = args.into_iter().skip(1);
                let (index, value) = if op == VecOp::SetBorrowed {
                    (Some(args.next().unwrap()), args.next().unwrap())
                } else {
                    (None, args.next().unwrap())
                };
                let Some(Value::Vector {
                    mut items,
                    mut capacity,
                    mut usable,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: borrowed vector"));
                };
                if let Some(index) = index {
                    let index = index_of(&index, items.len())?;
                    let old = std::mem::replace(&mut items[index], value);
                    self.heap.insert(
                        id,
                        Value::Vector {
                            items,
                            capacity,
                            usable,
                        },
                    );
                    self.drop_value(old)?;
                    return Ok(Value::Scalar(0));
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
                    usable =
                        box_allocation_capacity(16 + capacity * self.program.width(element) * 8);
                    self.stats.growth();
                }
                items.push(value);
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Scalar(0))
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
                    mut usable,
                }) = self.heap.take(id)
                else {
                    return Err(failure("internal ownership error: moved vector"));
                };
                if let Some(index) = index {
                    let index = index_of(&index, items.len())?;
                    let old = std::mem::replace(&mut items[index], value);
                    self.heap.insert(
                        id,
                        Value::Vector {
                            items,
                            capacity,
                            usable,
                        },
                    );
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
                    let requested = 16 + capacity * self.program.width(element) * 8;
                    if requested > usable {
                        usable = box_allocation_capacity(requested);
                    }
                    self.stats.growth();
                }
                items.push(value);
                self.heap.insert(
                    id,
                    Value::Vector {
                        items,
                        capacity,
                        usable,
                    },
                );
                Ok(Value::Owned(id))
            }
        }
    }
    /// Apply one or more checked callback steps in place. The vector's host
    /// item buffer and capacity are preserved unless `grow` is set, in which
    /// case the physical stride may grow/move under `{alloc, panic}`.
    fn vec_map_call(
        &mut self,
        id: usize,
        functions: Vec<Value>,
        grow: bool,
        target_width: usize,
        span: Span,
    ) -> Result<Value> {
        // Keep the live vector allocation represented while callbacks execute;
        // removing it would undercount peak-live when a callback allocates.
        let Some(Value::Vector {
            mut items,
            capacity,
            mut usable,
        }) = self.heap.take(id)
        else {
            return Err(Diagnostic::new(
                span,
                "internal ownership error: moved vector in map_in_place",
            ));
        };
        if grow {
            let requested = 16usize.saturating_add(
                capacity
                    .checked_mul(target_width)
                    .and_then(|words| words.checked_mul(8))
                    .unwrap_or(usize::MAX),
            );
            if requested > usable {
                usable = box_allocation_capacity(requested);
                self.stats.growth();
            }
        }
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
        self.heap.insert(
            id,
            Value::Vector {
                items,
                capacity,
                usable,
            },
        );
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
    fn host_result(&self, shape: ResultShape, status: i64, value: Value) -> Value {
        if status == 0 {
            Value::Enum {
                tag: shape.ok_tag,
                fields: vec![value],
            }
        } else {
            Value::Enum {
                tag: shape.err_tag,
                fields: vec![Value::Scalar(status)],
            }
        }
    }
    fn borrowed_bytes(&self, value: &Value) -> Option<Vec<u8>> {
        let Value::Borrowed(id) = value else {
            return None;
        };
        match self.heap.get(*id) {
            Some(Value::Buffer { data, .. }) => Some(data.clone()),
            _ => None,
        }
    }
    fn take_buffer(&mut self, value: &Value) -> Option<(usize, Vec<u8>, usize)> {
        let Value::Owned(id) = value else {
            return None;
        };
        match self.heap.take(*id) {
            Some(Value::Buffer { data, capacity }) => Some((*id, data, capacity)),
            _ => None,
        }
    }
    fn append_bounded(data: &mut Vec<u8>, capacity: usize, bytes: &[u8]) -> Option<i64> {
        if data.len() > capacity || bytes.len() > capacity - data.len() {
            return Some(27); // EFBIG
        }
        data.extend_from_slice(bytes);
        None
    }
    /// Reference implementation of the checked host operations. Its observable
    /// contract (buffer ownership, errno values, bounded reads, explicit
    /// timeouts) mirrors the generated native runtime; the two implementations
    /// share no host call path.
    fn host_call(
        &mut self,
        op: HostOp,
        shape: ResultShape,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value> {
        self.fuel = self
            .fuel
            .checked_sub(1)
            .ok_or_else(|| Diagnostic::new(span, "reference host computation budget exhausted"))?;
        let failure = |message: &str| Diagnostic::new(span, message.to_owned());
        match op {
            HostOp::FsRead => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.read path is not borrowed"))?;
                let (id, mut data, capacity) = self
                    .take_buffer(&args[1])
                    .ok_or_else(|| failure("internal error: FS.read buffer is not owned"))?;
                if path.contains(&0) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut file = match fs::File::open(path_from_bytes(&path)) {
                    Ok(file) => file,
                    Err(error) => {
                        self.stats.deallocation();
                        return Ok(self.host_result(
                            shape,
                            io_error_code(&error),
                            Value::Scalar(0),
                        ));
                    }
                };
                let initialized = data.len();
                data.resize(capacity, 0);
                let mut length = initialized;
                let mut probe = [0u8; 1];
                let status = loop {
                    self.fuel = self.fuel.checked_sub(1).ok_or_else(|| {
                        Diagnostic::new(span, "reference host computation budget exhausted")
                    })?;
                    let full = length == capacity;
                    let target: &mut [u8] = if full {
                        &mut probe[..]
                    } else {
                        &mut data[length..capacity]
                    };
                    match file.read(target) {
                        Ok(0) => break 0,
                        Ok(_) if full => break 27,
                        Ok(count) => length += count,
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(error) => break io_error_code(&error),
                    }
                };
                data.truncate(length);
                if status != 0 {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(self.host_result(shape, 0, Value::Owned(id)))
            }
            HostOp::FsWrite | HostOp::FsAppend => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: host path is not borrowed"))?;
                let data = self
                    .borrowed_bytes(&args[1])
                    .ok_or_else(|| failure("internal error: host data is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut options = OpenOptions::new();
                options.write(true).create(true);
                if op == HostOp::FsAppend {
                    options.append(true);
                } else {
                    options.truncate(true);
                }
                let status = match options.open(path_from_bytes(&path)) {
                    Ok(mut file) => match file.write_all(&data) {
                        Ok(()) => 0,
                        Err(error) => io_error_code(&error),
                    },
                    Err(error) => io_error_code(&error),
                };
                Ok(self.host_result(shape, status, Value::Scalar(data.len() as i64)))
            }
            HostOp::FsWriteExclusive => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: host path is not borrowed"))?;
                let data = self
                    .borrowed_bytes(&args[1])
                    .ok_or_else(|| failure("internal error: host data is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut options = OpenOptions::new();
                options.write(true).create_new(true);
                #[cfg(unix)]
                {
                    use std::os::unix::fs::OpenOptionsExt;
                    options.mode(0o600);
                }
                let status = match options.open(path_from_bytes(&path)) {
                    Ok(mut file) => match file.write_all(&data) {
                        Ok(()) => 0,
                        Err(error) => io_error_code(&error),
                    },
                    Err(error) => io_error_code(&error),
                };
                Ok(self.host_result(shape, status, Value::Scalar(data.len() as i64)))
            }
            HostOp::FsRemove => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.remove path is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let status = fs::remove_file(path_from_bytes(&path))
                    .err()
                    .map_or(0, |error| io_error_code(&error));
                Ok(self.host_result(shape, status, Value::Scalar(0)))
            }
            HostOp::FsRename => {
                let from = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.rename source is not borrowed"))?;
                let to = self.borrowed_bytes(&args[1]).ok_or_else(|| {
                    failure("internal error: FS.rename destination is not borrowed")
                })?;
                if from.contains(&0) || to.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let status = fs::rename(path_from_bytes(&from), path_from_bytes(&to))
                    .err()
                    .map_or(0, |error| io_error_code(&error));
                Ok(self.host_result(shape, status, Value::Scalar(0)))
            }
            HostOp::FsMkdir => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.mkdir path is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let status = fs::create_dir(path_from_bytes(&path))
                    .err()
                    .map_or(0, |error| io_error_code(&error));
                Ok(self.host_result(shape, status, Value::Scalar(0)))
            }
            HostOp::FsRemoveDir => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.remove_dir path is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let status = fs::remove_dir(path_from_bytes(&path))
                    .err()
                    .map_or(0, |error| io_error_code(&error));
                Ok(self.host_result(shape, status, Value::Scalar(0)))
            }
            HostOp::FsList => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS.list path is not borrowed"))?;
                let (id, mut data, capacity) = self
                    .take_buffer(&args[1])
                    .ok_or_else(|| failure("internal error: FS.list buffer is not owned"))?;
                if path.contains(&0) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut status = 0;
                match fs::read_dir(path_from_bytes(&path)) {
                    Ok(entries) => {
                        for entry in entries {
                            match entry {
                                Ok(entry) => {
                                    let name = os_bytes(entry.file_name());
                                    if let Some(failure) = Self::append_bounded(
                                        &mut data, capacity, &name,
                                    )
                                    .or_else(|| Self::append_bounded(&mut data, capacity, b"\n"))
                                    {
                                        status = failure;
                                        break;
                                    }
                                }
                                Err(error) => {
                                    status = io_error_code(&error);
                                    break;
                                }
                            }
                        }
                    }
                    Err(error) => status = io_error_code(&error),
                }
                if status != 0 {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(self.host_result(shape, 0, Value::Owned(id)))
            }
            HostOp::FsIsFile | HostOp::FsIsDir | HostOp::FsSize | HostOp::FsExists => {
                let path = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: FS metadata path is not borrowed"))?;
                if path.contains(&0) {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                match fs::metadata(path_from_bytes(&path)) {
                    Ok(metadata) => {
                        let value = match op {
                            HostOp::FsIsFile => (metadata.is_file() as i64, 0),
                            HostOp::FsIsDir => (metadata.is_dir() as i64, 0),
                            HostOp::FsExists => (1, 0),
                            HostOp::FsSize => match i64::try_from(metadata.len()) {
                                Ok(size) => (size, 0),
                                Err(_) => (0, 75), // EOVERFLOW
                            },
                            _ => unreachable!(),
                        };
                        Ok(self.host_result(shape, value.1, Value::Scalar(value.0)))
                    }
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::NotFound | io::ErrorKind::NotADirectory
                        ) =>
                    {
                        let status = if op == HostOp::FsSize {
                            io_error_code(&error)
                        } else {
                            0
                        };
                        Ok(self.host_result(shape, status, Value::Scalar(0)))
                    }
                    Err(error) => {
                        Ok(self.host_result(shape, io_error_code(&error), Value::Scalar(0)))
                    }
                }
            }
            HostOp::EnvArgCount => {
                let count = self.host.args.len();
                Ok(self.host_result(shape, 0, Value::Scalar(count as i64)))
            }
            HostOp::EnvArg => {
                let index = args[0].scalar();
                let (id, mut data, capacity) = self
                    .take_buffer(&args[1])
                    .ok_or_else(|| failure("internal error: ENV.arg buffer is not owned"))?;
                let Some(index) = usize::try_from(index)
                    .ok()
                    .filter(|index| *index < self.host.args.len())
                else {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 2, Value::Scalar(0)));
                };
                let value = self.host.args[index].clone();
                if let Some(status) = Self::append_bounded(&mut data, capacity, &value) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(self.host_result(shape, 0, Value::Owned(id)))
            }
            HostOp::EnvVarCount => {
                let count = self.host.environment.len();
                Ok(self.host_result(shape, 0, Value::Scalar(count as i64)))
            }
            HostOp::EnvVar => {
                let name = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: ENV.var name is not borrowed"))?;
                let (id, mut data, capacity) = self
                    .take_buffer(&args[1])
                    .ok_or_else(|| failure("internal error: ENV.var buffer is not owned"))?;
                if name.contains(&0) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let Some(value) = self.host.var(&name).map(<[u8]>::to_vec) else {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 2, Value::Scalar(0)));
                };
                if let Some(status) = Self::append_bounded(&mut data, capacity, &value) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(self.host_result(shape, 0, Value::Owned(id)))
            }
            HostOp::TimeUnixSeconds => {
                let seconds = match SystemTime::now().duration_since(UNIX_EPOCH) {
                    Ok(duration) => i64::try_from(duration.as_secs()).unwrap_or(i64::MAX),
                    Err(error) => -i64::try_from(error.duration().as_secs()).unwrap_or(i64::MAX),
                };
                Ok(self.host_result(shape, 0, Value::Scalar(seconds)))
            }
            HostOp::TimeMonotonicNs => {
                Ok(self.host_result(shape, 0, Value::Scalar(self.host.monotonic_ns())))
            }
            HostOp::TimeSleepMs => {
                let milliseconds = args[0].scalar();
                if milliseconds < 0 {
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                thread::sleep(Duration::from_millis(milliseconds as u64));
                Ok(self.host_result(shape, 0, Value::Scalar(0)))
            }
            HostOp::ProcRun => {
                let program = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: PROC.run program is not borrowed"))?;
                let arguments = self.borrowed_bytes(&args[1]).ok_or_else(|| {
                    failure("internal error: PROC.run arguments are not borrowed")
                })?;
                let timeout = args[3].scalar();
                let Value::Borrowed(id) = args[2] else {
                    return Err(failure("internal error: PROC.run output is not borrowed"));
                };
                let Some(Value::Buffer { data, capacity }) = self.heap.take(id) else {
                    return Err(failure("internal error: PROC.run output is not a buffer"));
                };
                let initialized = data.len();
                let mut data = data;
                if timeout < 0 || program.is_empty() || program.contains(&0) {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut command = Command::new(value_bytes(&program));
                command
                    .args(split_nul(&arguments))
                    .stdin(Stdio::null())
                    .stdout(Stdio::piped())
                    .stderr(Stdio::null());
                let mut child = match command.spawn() {
                    Ok(child) => child,
                    Err(error) => {
                        self.heap.insert(id, Value::Buffer { data, capacity });
                        return Ok(self.host_result(
                            shape,
                            io_error_code(&error),
                            Value::Scalar(0),
                        ));
                    }
                };
                let mut stdout = child.stdout.take().expect("piped stdout");
                let limit = capacity - initialized;
                let overflow_flag = Arc::new(AtomicBool::new(false));
                let reader_overflow = overflow_flag.clone();
                let deadline =
                    (timeout != 0).then(|| Instant::now() + Duration::from_millis(timeout as u64));
                let mut timed_out = false;
                // Reader state mirrors the native pipe loop: running, EOF, or
                // a read error (native kills and reports the errno then).
                let reader_state = Arc::new(AtomicU8::new(0));
                let spawn_state = reader_state.clone();
                let reader = thread::spawn(move || {
                    let mut captured = Vec::new();
                    let mut buffer = [0u8; 4096];
                    let mut overflow = false;
                    let mut read_error = None;
                    loop {
                        match stdout.read(&mut buffer) {
                            Ok(0) => break,
                            Ok(count) => {
                                if captured.len() + count > limit {
                                    let room = limit.saturating_sub(captured.len());
                                    captured.extend_from_slice(&buffer[..room]);
                                    overflow = true;
                                    reader_overflow.store(true, Ordering::Relaxed);
                                    break;
                                }
                                captured.extend_from_slice(&buffer[..count]);
                            }
                            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                            Err(error) => {
                                read_error = Some(io_error_code(&error));
                                break;
                            }
                        }
                    }
                    let outcome = (captured, overflow, read_error);
                    spawn_state.store(if outcome.2.is_some() { 2 } else { 1 }, Ordering::Relaxed);
                    outcome
                });
                let mut status: Option<std::process::ExitStatus> = None;
                loop {
                    match child.try_wait() {
                        Ok(Some(exit)) => {
                            status = Some(exit);
                            break;
                        }
                        Ok(None) => {}
                        Err(_) => {
                            let _ = child.kill();
                            let _ = child.wait();
                            break;
                        }
                    }
                    // An overflowing pipe or a reader failure ends the wait
                    // like the native poll loop: the post-join status decides
                    // which errno wins.
                    if reader_state.load(Ordering::Relaxed) == 2
                        || overflow_flag.load(Ordering::Relaxed)
                    {
                        break;
                    }
                    if deadline.is_some_and(|deadline| Instant::now() >= deadline) {
                        timed_out = true;
                        break;
                    }
                    thread::sleep(Duration::from_millis(2));
                }
                if status.is_none() {
                    let _ = child.kill();
                    let _ = child.wait();
                }
                let (captured, overflow, read_error) = reader.join().unwrap();
                let append_status = Self::append_bounded(&mut data, capacity, &captured);
                self.heap.insert(id, Value::Buffer { data, capacity });
                // Overflow beats a concurrent deadline like the native loop,
                // which breaks the pipe loop before its timeout can re-arm.
                if overflow {
                    return Ok(self.host_result(shape, 27, Value::Scalar(0)));
                }
                if let Some(error) = read_error {
                    return Ok(self.host_result(shape, error, Value::Scalar(0)));
                }
                if timed_out {
                    return Ok(self.host_result(shape, 110, Value::Scalar(0)));
                }
                let Some(status) = status else {
                    return Ok(self.host_result(shape, 5, Value::Scalar(0)));
                };
                if let Some(status_code) = append_status {
                    return Ok(self.host_result(shape, status_code, Value::Scalar(0)));
                }
                Ok(self.host_result(shape, 0, Value::Scalar(exit_status_code(status))))
            }
            HostOp::NetTcpExchange => {
                let host = self
                    .borrowed_bytes(&args[0])
                    .ok_or_else(|| failure("internal error: NET host is not borrowed"))?;
                let request = self
                    .borrowed_bytes(&args[2])
                    .ok_or_else(|| failure("internal error: NET request is not borrowed"))?;
                let port = args[1].scalar();
                let timeout_ms = args[4].scalar();
                let Value::Borrowed(id) = args[3] else {
                    return Err(failure("internal error: NET response is not borrowed"));
                };
                let Some(Value::Buffer { data, capacity }) = self.heap.take(id) else {
                    return Err(failure("internal error: NET response is not a buffer"));
                };
                let mut data = data;
                let invalid = || self.host_result(shape, 22, Value::Scalar(0));
                if host.contains(&0) {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(invalid());
                }
                let Ok(host) = String::from_utf8(host) else {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(invalid());
                };
                let Ok(port) = u16::try_from(port) else {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(invalid());
                };
                if port == 0 || timeout_ms < 0 {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(invalid());
                }
                let duration = Duration::from_millis(timeout_ms as u64);
                // One shared deadline across connect, send, and receive mirrors
                // the native implementation: no phase can restart the budget.
                let deadline = if timeout_ms != 0 {
                    Some(Instant::now() + duration)
                } else {
                    None
                };
                let remaining =
                    || deadline.map(|deadline| deadline.saturating_duration_since(Instant::now()));
                let connect = if timeout_ms == 0 {
                    TcpStream::connect((host.as_str(), port))
                } else {
                    match (host.as_str(), port).to_socket_addrs() {
                        Ok(addresses) => {
                            // A successful resolution with zero addresses
                            // fails like the native empty list: refused.
                            let mut last = io::Error::from_raw_os_error(111);
                            let mut connected = None;
                            for address in addresses {
                                let Some(left) = remaining().filter(|left| !left.is_zero()) else {
                                    last = io::Error::from_raw_os_error(110);
                                    break;
                                };
                                match TcpStream::connect_timeout(&address, left) {
                                    Ok(stream) => {
                                        connected = Some(stream);
                                        break;
                                    }
                                    Err(error) => {
                                        let timed_out = error.kind() == io::ErrorKind::TimedOut;
                                        last = error;
                                        if timed_out {
                                            break;
                                        }
                                    }
                                }
                            }
                            connected.ok_or(last)
                        }
                        Err(error) => Err(error),
                    }
                };
                let mut stream = match connect {
                    Ok(stream) => stream,
                    Err(error) => {
                        self.heap.insert(id, Value::Buffer { data, capacity });
                        return Ok(self.host_result(
                            shape,
                            io_error_code(&error),
                            Value::Scalar(0),
                        ));
                    }
                };
                if timeout_ms != 0 {
                    let _ = stream.set_read_timeout(remaining());
                    let _ = stream.set_write_timeout(remaining());
                }
                let mut send_status = 0;
                if timeout_ms == 0 {
                    if let Err(error) = stream.write_all(&request) {
                        send_status = io_error_code(&error);
                    }
                } else {
                    // Retrying partial writes until the shared deadline keeps
                    // the total budget bounded like the native send loop.
                    let mut sent = 0usize;
                    while sent < request.len() {
                        let Some(left) = remaining().filter(|left| !left.is_zero()) else {
                            send_status = 110;
                            break;
                        };
                        let _ = stream.set_write_timeout(Some(left));
                        match stream.write(&request[sent..]) {
                            Ok(0) => {
                                send_status = 5;
                                break;
                            }
                            Ok(count) => sent += count,
                            Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                            Err(error)
                                if matches!(
                                    error.kind(),
                                    io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                                ) =>
                            {
                                send_status = 110;
                                break;
                            }
                            Err(error) => {
                                send_status = io_error_code(&error);
                                break;
                            }
                        }
                    }
                    let _ = stream.set_write_timeout(remaining());
                }
                if send_status != 0 {
                    self.heap.insert(id, Value::Buffer { data, capacity });
                    return Ok(self.host_result(shape, send_status, Value::Scalar(0)));
                }
                let _ = stream.shutdown(Shutdown::Write);
                let initialized = data.len();
                data.resize(capacity, 0);
                let mut length = initialized;
                let mut received_total = 0i64;
                let mut probe = [0u8; 1];
                let status = loop {
                    self.fuel = self.fuel.checked_sub(1).ok_or_else(|| {
                        Diagnostic::new(span, "reference host computation budget exhausted")
                    })?;
                    let full = length == capacity;
                    let target: &mut [u8] = if full {
                        &mut probe[..]
                    } else {
                        &mut data[length..capacity]
                    };
                    if timeout_ms != 0 {
                        // Each wait is the remaining shared budget, so a slow
                        // sender cannot extend the total past the deadline.
                        match remaining().filter(|left| !left.is_zero()) {
                            Some(left) => {
                                let _ = stream.set_read_timeout(Some(left));
                            }
                            None => break 110,
                        }
                    }
                    match stream.read(target) {
                        Ok(0) => break 0,
                        Ok(_) if full => break 27,
                        Ok(count) => {
                            length += count;
                            received_total += count as i64;
                        }
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => continue,
                        Err(error)
                            if matches!(
                                error.kind(),
                                io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                            ) =>
                        {
                            break 110;
                        }
                        Err(error) => break io_error_code(&error),
                    }
                };
                data.truncate(length);
                self.heap.insert(id, Value::Buffer { data, capacity });
                if status != 0 {
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                Ok(self.host_result(shape, 0, Value::Scalar(received_total)))
            }
            HostOp::OsStrerror => {
                let code = args[0].scalar();
                let (id, mut data, capacity) = self
                    .take_buffer(&args[1])
                    .ok_or_else(|| failure("internal error: OS.strerror buffer is not owned"))?;
                if !(0..=4095).contains(&code) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, 22, Value::Scalar(0)));
                }
                let mut text = io::Error::from_raw_os_error(code as i32).to_string();
                if let Some(at) = text.rfind(" (os error ") {
                    text.truncate(at);
                }
                if let Some(status) = Self::append_bounded(&mut data, capacity, text.as_bytes()) {
                    self.stats.deallocation();
                    return Ok(self.host_result(shape, status, Value::Scalar(0)));
                }
                self.heap.insert(id, Value::Buffer { data, capacity });
                Ok(self.host_result(shape, 0, Value::Owned(id)))
            }
        }
    }
    fn consume(&self, expr: &Expr, frame: &mut Frame) {
        if let Some(id) = expr.resource {
            frame.resources[id] = None;
        }
    }
    fn local_active(&self, slot: usize, frame: &mut Frame) {
        if let Some(id) = self.program.functions[frame.function].local_resources[slot] {
            // A pinned aggregate local keeps its live storage in the cell.
            // The resource entry aliases that cell instead of snapshotting it,
            // so a replacement through `&mut` or `*p = value` is observed and
            // dropped exactly once at scope exit.
            frame.resources[id] = Some(match &frame.locals[slot] {
                Value::RecordCell(cell) | Value::ArrayCell(cell) => Value::RecordCell(cell.clone()),
                value => self.materialize(value.clone()),
            });
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
            Value::RecordCell(cell) | Value::ArrayCell(cell) => {
                let value = std::mem::replace(&mut *cell.lock().unwrap(), Value::Scalar(0));
                self.drop_value(value)?;
            }
            Value::Union { value, .. } => self.drop_value(*value)?,
            Value::DynObject { value, .. } => {
                let payload = match Arc::try_unwrap(value) {
                    Ok(cell) => cell.into_inner().unwrap(),
                    Err(cell) => cell.lock().unwrap().clone(),
                };
                self.stats.deallocation();
                self.drop_value(payload)?;
            }
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
            Value::DynArray { items, .. } => {
                for item in items.into_iter().rev() {
                    self.drop_value(item)?;
                }
            }
            Value::Allocator { .. } => {}
            Value::AllocatorContext(state) => {
                self.allocator_context_release(&state)?;
            }
            Value::AllocBox(state) => {
                self.drop_value(state.payload)?;
                self.allocator_release(&state.allocator, state.block, Span::default())?;
                self.release_allocator_binding(state.allocator)?;
            }
            Value::AllocVector(state) => {
                for item in state.items.into_iter().rev() {
                    self.drop_value(item)?;
                }
                if let Some(block) = state.block {
                    self.allocator_release(&state.allocator, block, Span::default())?;
                }
                self.release_allocator_binding(state.allocator)?;
            }
            // A slice view borrows its base and owns nothing.
            Value::Slice(_) => {}
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
    /// Dynamic frames a child task may inherit at spawn. Only copyable
    /// noncapturing `fn` handlers cross the boundary; the longest such bottom
    /// prefix is copied. A capturing or one-shot frame is a barrier, because
    /// its environment is owned by the parent's dynamic extent and must not be
    /// shared or duplicated.
    fn inheritable_handlers(&self) -> Vec<(usize, usize)> {
        let mut inherited = Vec::new();
        // Walk the frames visible here: a redirect frame skips the frames a
        // handler pushed around the resumption that pushed it.
        let mut index = self.dynamic_handlers.len();
        while index > 0 {
            index -= 1;
            let frame = &self.dynamic_handlers[index];
            if let Some(target) = frame.redirect {
                index = target;
                continue;
            }
            if frame.consume {
                break;
            }
            let Some(Value::Function {
                function,
                environment: None,
            }) = frame.handler.as_ref()
            else {
                break;
            };
            inherited.push((frame.operation, *function));
        }
        inherited.reverse();
        inherited
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
    /// Resolve the registered member vtable and call the selected checked
    /// method. The receiver value is already adapted to the impl's receiver
    /// mode (owned payload, payload-cell reference, or mutable cell reference).
    /// Map an owned object's member identifier from `from`'s member table to
    /// `to`'s. The payload cell moves unchanged: nothing is allocated, copied,
    /// or released.
    fn dyn_upcast(&self, from: usize, to: usize, value: Value, span: Span) -> Result<Value> {
        let Value::DynObject { member, value } = value else {
            return Err(Diagnostic::new(
                span,
                "internal error: a trait-object upcast expected an owned object",
            ));
        };
        let member_type = self
            .program
            .dyn_members
            .get(from)
            .and_then(|members| members.get(member))
            .map(|entry| entry.member);
        let target = member_type.and_then(|member_type| {
            self.program
                .dyn_members
                .get(to)?
                .iter()
                .position(|entry| entry.member == member_type)
        });
        let Some(member) = target else {
            return Err(Diagnostic::new(
                span,
                "internal error: an upcast member is not registered in the target object",
            ));
        };
        Ok(Value::DynObject { member, value })
    }
    fn call_dyn_member(
        &mut self,
        spec: &DynCallSpec,
        member: usize,
        args: Vec<Value>,
        span: Span,
    ) -> Result<Value> {
        let entry = self
            .program
            .dyn_members
            .get(spec.object)
            .and_then(|members| members.get(member))
            .ok_or_else(|| {
                Diagnostic::new(
                    span,
                    format!(
                        "internal error: no registered member {member} for dynamic object '{}'",
                        spec.trait_name
                    ),
                )
            })?;
        let function = *entry.methods.get(&spec.key).ok_or_else(|| {
            Diagnostic::new(
                span,
                format!(
                    "internal error: member of dynamic object '{}' has no dynamic method '{}'",
                    self.program
                        .dyn_object_names
                        .get(spec.object)
                        .map(String::as_str)
                        .unwrap_or("<unknown>"),
                    spec.method
                ),
            )
        })?;
        // The receiver has no grade; the remaining logical arguments drop any
        // grade-zero position before the physical call.
        let mut args = args.into_iter();
        let receiver = args.next().expect("dynamic call has a receiver");
        let mut physical = vec![receiver];
        for (index, value) in args.enumerate() {
            if !spec
                .parameter_grades
                .get(index)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                physical.push(value);
            }
        }
        self.call(function, physical)
    }
    fn call(&mut self, index: usize, args: Vec<Value>) -> Result<Value> {
        self.call_with(index, vec![], args)
    }
    fn call_with(&mut self, index: usize, captures: Vec<Value>, args: Vec<Value>) -> Result<Value> {
        let f = &self.program.functions[index];
        let erased_result = f.result_grade.is_some_and(Grade::is_zero);
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
        let slot_of = |position: usize| {
            f.parameter_slots
                .as_ref()
                .map_or(position, |slots| slots[position])
        };
        let capture_count = captures.len();
        for (position, capture) in captures.into_iter().enumerate() {
            frame.locals[slot_of(position)] = capture;
            self.local_active(slot_of(position), &mut frame);
        }
        let mut args = args.into_iter();
        for position in capture_count..f.parameters {
            let slot = slot_of(position);
            if f.parameter_grades
                .get(position)
                .copied()
                .flatten()
                .is_some_and(Grade::is_zero)
            {
                // Grade-zero parameter: no ABI argument exists and its local
                // slot is never observed. Leave it as the dummy scalar.
                continue;
            }
            let Some(value) = args.next() else {
                return Err(Diagnostic::new(
                    f.span,
                    "internal error: missing physical argument for a call",
                ));
            };
            frame.locals[slot] = value;
            self.local_active(slot, &mut frame);
        }
        if args.next().is_some() {
            return Err(Diagnostic::new(
                f.span,
                "internal error: too many physical arguments for a call",
            ));
        }
        let result = self.block(&f.body, &mut frame);
        self.depth -= 1;
        let flow = result?;
        self.cleanup(&mut frame)?;
        Ok(match flow {
            Flow::Value(v) | Flow::Return(v) => {
                if erased_result {
                    self.drop_value(v)?;
                    Value::Scalar(0)
                } else {
                    v
                }
            }
            Flow::Break(_) | Flow::Continue | Flow::Exit(..) => {
                unreachable!("loop and region exits are checked")
            }
        })
    }
    fn block(&mut self, block: &Block, frame: &mut Frame) -> Result<Flow> {
        let mut slots = Vec::new();
        for statement in &block.statements {
            match statement {
                Statement::Declare(slot) => {
                    // Hidden temporary-owner storage. Initialization happens
                    // at its source evaluation point; cleanup is conditional
                    // on that initialization having become active.
                    slots.push(*slot);
                }
                Statement::Let(slot, expr) => {
                    let value = value!(self.expr(expr, frame));
                    self.consume(expr, frame);
                    if self.erased_local(*slot, frame) {
                        // Erased bindings have no storage. Affine owned values
                        // are destroyed eagerly exactly once; linear ones are
                        // rejected by the checker.
                        if self.program.owns(expr.ty) {
                            self.drop_value(value)?;
                        }
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
    #[inline(never)]
    fn handler_push(
        &mut self,
        operation: usize,
        handler: &Expr,
        body: &Block,
        frame: &mut Frame,
    ) -> Result<Flow> {
        let handler_value = value!(self.expr(handler, frame));
        self.consume(handler, frame);
        let consume = matches!(handler.ty, Type::Once(_));
        self.dynamic_handlers.push(HandlerFrame {
            operation,
            handler: Some(handler_value),
            redirect: None,
            consume,
        });
        let flow = self.block(body, frame);
        let popped = self.dynamic_handlers.pop();
        if let Some(HandlerFrame {
            handler: Some(value),
            ..
        }) = popped
        {
            self.drop_value(value)?;
        }
        flow
    }
    #[inline(never)]
    fn dynamic_perform(
        &mut self,
        expr: &Expr,
        operation: usize,
        payload: &Expr,
        resume: &Expr,
        frame: &mut Frame,
    ) -> Result<Flow> {
        let mut index = self.dynamic_handlers.len();
        let found = loop {
            if index == 0 {
                break None;
            }
            index -= 1;
            let candidate = &self.dynamic_handlers[index];
            if let Some(target) = candidate.redirect {
                index = target;
                continue;
            }
            if candidate.operation == operation {
                // A consumed once frame still discharges its operation: a
                // later perform must not fall through to an outer handler.
                break candidate.handler.is_some().then_some(index);
            }
        };
        let Some(index) = found else {
            return Err(Diagnostic::new(
                expr.span,
                "no dynamically active handler for this operation",
            ));
        };
        let payload_value = value!(self.expr(payload, frame));
        let resume_value = value!(self.expr(resume, frame));
        self.consume(payload, frame);
        self.consume(resume, frame);
        let consume = self.dynamic_handlers[index].consume;
        if consume {
            let handler = self.dynamic_handlers[index]
                .handler
                .take()
                .expect("handler presence checked above");
            Ok(Flow::Value(
                self.call_value(handler, vec![payload_value, resume_value])?,
            ))
        } else {
            let function = match self.dynamic_handlers[index].handler.as_ref() {
                Some(Value::Function {
                    function,
                    environment: None,
                }) => *function,
                _ => {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: copyable dynamic effect handler must be a noncapturing function",
                    ));
                }
            };
            Ok(Flow::Value(
                self.call(function, vec![payload_value, resume_value])?,
            ))
        }
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
    // Keep allocation temporaries out of the frame used by every expression.
    // Debug builds otherwise exhaust ordinary test-thread stacks while parsing
    // valid nested JSON before the evaluator's checked depth limit is reached.
    #[inline(never)]
    fn expression_allocations(&mut self, expr: &Expr, frame: &mut Frame) -> Result<Flow> {
        let value = match &expr.kind {
            ExprKind::BoxNew(arg) => {
                let value = value!(self.expr(arg, frame));
                self.consume(arg, frame);
                self.allocate_box(value, self.program.width(arg.ty))
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
            ExprKind::BoxWrite(reference, replacement) => {
                let reference = value!(self.expr(reference, frame));
                let Value::Borrowed(id) = reference else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: box write has no borrowed box",
                    ));
                };
                let value = value!(self.expr(replacement, frame));
                self.consume(replacement, frame);
                if self.heap.get(id).is_none() {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: dangling box write",
                    ));
                }
                self.heap.insert(id, value);
                Value::Scalar(0)
            }
            ExprKind::BoxReuse { owner, payload } => {
                let Value::Owned(id) = value!(self.expr(owner, frame)) else {
                    unreachable!("checked Box.reuse owner")
                };
                let new = value!(self.expr(payload, frame));
                let capacity = self.heap.box_capacity(id);
                // Both arguments have been evaluated. Only now is the old
                // affine payload destroyed. The outer allocation is preserved.
                self.consume(owner, frame);
                self.consume(payload, frame);
                let old = self.heap.take(id).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal ownership error: stale reuse box")
                })?;
                self.drop_value(old)?;
                self.heap.insert(id, new);
                self.heap.set_box_capacity(id, capacity);
                self.stats.reuse();
                Value::Owned(id)
            }
            ExprKind::BoxReuseGrow { owner, payload } => {
                let Value::Owned(id) = value!(self.expr(owner, frame)) else {
                    unreachable!("checked Box.reuse_grow owner")
                };
                let new = value!(self.expr(payload, frame));
                let retained = self.heap.box_capacity(id);
                let requested = self.program.width(payload.ty) * 8;
                let capacity = if requested > retained {
                    box_allocation_capacity(requested)
                } else {
                    retained
                };
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
                self.heap.set_box_capacity(id, capacity);
                self.stats.reuse();
                Value::Owned(id)
            }
            ExprKind::ArenaNew => self.arena_new_value(None),
            ExprKind::ArenaNewWith { strategy } => {
                let strategy = value!(self.expr(strategy, frame));
                let Value::Function {
                    function,
                    environment: None,
                } = strategy
                else {
                    unreachable!("checked arena strategy is a noncapturing function")
                };
                self.arena_new_value(Some(function))
            }
            ExprKind::ArenaAlloc { arena, value } => {
                let Value::ArenaRef(state) = value!(self.expr(arena, frame)) else {
                    unreachable!("checked arena borrow")
                };
                let payload = value!(self.expr(value, frame));
                let bytes = self.program.width(value.ty) * 8;
                self.consume(arena, frame);
                self.consume(value, frame);
                self.arena_allocate(&state, payload, bytes)?
            }
            ExprKind::ArenaTryAlloc {
                arena,
                value: argument,
                shape,
            } => {
                let Value::ArenaRef(state) = value!(self.expr(arena, frame)) else {
                    unreachable!("checked arena borrow")
                };
                let payload = value!(self.expr(argument, frame));
                let bytes = self.program.width(argument.ty) * 8;
                self.consume(arena, frame);
                self.consume(argument, frame);
                match self.arena_try_allocate(&state, payload, bytes)? {
                    Ok(owner) => Value::Enum {
                        tag: shape.ok_tag,
                        fields: vec![owner],
                    },
                    Err(payload) => Value::Enum {
                        tag: shape.err_tag,
                        fields: vec![payload],
                    },
                }
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
            ExprKind::AllocatorNew {
                alloc,
                free,
                realloc,
            } => {
                let alloc = value!(self.expr(alloc, frame));
                let free = value!(self.expr(free, frame));
                let Value::Function {
                    function: alloc_function,
                    environment: None,
                } = alloc
                else {
                    unreachable!("checked allocator allocation callback")
                };
                let Value::Function {
                    function: free_function,
                    environment: None,
                } = free
                else {
                    unreachable!("checked allocator release callback")
                };
                let realloc_function = match realloc {
                    Some(realloc) => {
                        let realloc = value!(self.expr(realloc, frame));
                        let Value::Function {
                            function,
                            environment: None,
                        } = realloc
                        else {
                            unreachable!("checked allocator growth callback")
                        };
                        Some(function)
                    }
                    None => None,
                };
                Value::Allocator {
                    alloc: alloc_function,
                    free: free_function,
                    realloc: realloc_function,
                }
            }
            ExprKind::AllocatorContextNew {
                value: argument,
                spec,
            } => {
                let instance = value!(self.expr(argument, frame));
                self.consume(argument, frame);
                let Some(spec) = self.program.allocator_contexts.get(*spec).copied() else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: allocator context has no checked method set",
                    ));
                };
                // Two compiler-owned cells: the state block (counted here) and
                // the context metadata (the owning heap cell below). The
                // instance's own owners live inside the state.
                self.stats.allocation();
                let _ = spec.state;
                let context = AllocatorContextState {
                    references: std::sync::atomic::AtomicUsize::new(1),
                    instance: Arc::new(Mutex::new(instance)),
                    alloc: spec.alloc,
                    free: spec.free,
                    grow: spec.grow,
                };
                self.allocate(Value::AllocatorContext(Arc::new(context)))
            }
            ExprKind::AllocatorContextShare(argument) => {
                let state = match value!(self.expr(argument, frame)) {
                    Value::Borrowed(id) => {
                        let Some(Value::AllocatorContext(state)) = self.heap.get(id) else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: dangling allocator context borrow",
                            ));
                        };
                        state
                    }
                    Value::AllocatorContextRef(state) => state,
                    _ => unreachable!("checked allocator context borrow"),
                };
                state
                    .references
                    .fetch_add(1, std::sync::atomic::Ordering::SeqCst);
                Value::AllocatorContext(state)
            }
            ExprKind::AllocBoxNew { allocator, value } => {
                let allocator_ast = allocator;
                let allocator = value!(self.expr(allocator_ast, frame));
                let payload = value!(self.expr(value, frame));
                let bytes = self.program.width(value.ty) * 8;
                self.consume(value, frame);
                if allocator_ast.ty == Type::AllocatorContext {
                    self.consume(allocator_ast, frame);
                }
                self.eval_alloc_box_new(allocator, payload, bytes, expr.span)?
            }
            ExprKind::AllocBoxTryNew {
                allocator,
                value: argument,
                shape,
            } => {
                let allocator_ast = allocator;
                let allocator = value!(self.expr(allocator_ast, frame));
                let payload = value!(self.expr(argument, frame));
                let bytes = self.program.width(argument.ty) * 8;
                self.consume(argument, frame);
                if allocator_ast.ty == Type::AllocatorContext {
                    self.consume(allocator_ast, frame);
                }
                self.eval_alloc_box_try_new(allocator, payload, bytes, *shape, expr.span)?
            }
            ExprKind::AllocBoxRead(argument) => {
                let Value::Borrowed(id) = value!(self.expr(argument, frame)) else {
                    unreachable!("checked allocator box borrow")
                };
                let Some(Value::AllocBox(state)) = self.heap.get(id) else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: dangling allocator box borrow",
                    ));
                };
                state.payload
            }
            ExprKind::AllocBoxTake(argument) => {
                let Value::Owned(id) = value!(self.expr(argument, frame)) else {
                    unreachable!("checked allocator box take")
                };
                self.consume(argument, frame);
                let Some(Value::AllocBox(state)) = self.heap.take(id) else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal ownership error: stale allocator box",
                    ));
                };
                self.stats.deallocation();
                self.allocator_release(&state.allocator, state.block, expr.span)?;
                self.release_allocator_binding(state.allocator)?;
                state.payload
            }
            ExprKind::AllocVecNew {
                allocator,
                capacity,
                element,
            } => {
                let allocator_ast = allocator;
                let allocator = value!(self.expr(allocator_ast, frame));
                let capacity = match capacity {
                    Some(capacity) => {
                        let requested = value!(self.expr(capacity, frame)).scalar();
                        Some(usize::try_from(requested).map_err(|_| {
                            Diagnostic::new(expr.span, "panic: negative AllocVec capacity")
                        })?)
                    }
                    None => None,
                };
                if allocator_ast.ty == Type::AllocatorContext {
                    self.consume(allocator_ast, frame);
                }
                self.eval_alloc_vec_new(
                    allocator,
                    capacity,
                    self.program.width(*element),
                    expr.span,
                )?
            }
            ExprKind::BoxTryNew {
                value: argument,
                shape,
            } => {
                let value = value!(self.expr(argument, frame));
                self.consume(argument, frame);
                if self.try_charge() {
                    let owner = self.allocate_box(value, self.program.width(argument.ty));
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
                let retained = self.heap.box_capacity(id);
                let requested = self.program.width(payload.ty) * 8;
                // Capacity includes native size-class rounding and survives
                // narrowing reuse. Only a physical growth spends the budget.
                let grows = requested > retained;
                if !grows || self.try_charge() {
                    let previous = self.heap.take(id).ok_or_else(|| {
                        Diagnostic::new(expr.span, "internal ownership error: stale reuse box")
                    })?;
                    self.drop_value(previous)?;
                    self.heap.insert(id, new);
                    // Native fallible growth uses an exact-sized system block
                    // rather than the infallible path's size-class rounding.
                    self.heap
                        .set_box_capacity(id, if grows { requested } else { retained });
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
            _ => unreachable!("expression dispatched to the wrong evaluator helper"),
        };
        Ok(Flow::Value(value))
    }
    #[inline(never)]
    fn expression_call(&mut self, expr: &Expr, frame: &mut Frame) -> Result<Flow> {
        let panic = || Diagnostic::new(expr.span, "panic: checked arithmetic failed");
        let value = match &expr.kind {
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
                    Target::Host(op, shape) => self.host_call(*op, *shape, values, expr.span)?,
                    Target::Bytes(op) => self.bytes_call(*op, values, expr.span)?,
                    Target::String(op) => self.string_call(*op, values, expr.span)?,
                    Target::Str(op) => self.str_call(*op, values, expr.span)?,
                    Target::Vec(op, element) => self.vec_call(*op, *element, values, expr.span)?,
                    Target::Slice(op, _) => self.slice_call(*op, values, expr.span)?,
                    Target::DynArray(op, element) => {
                        self.dyn_array_call(*op, *element, values, expr.span)?
                    }
                    Target::AllocVec(op, element) => {
                        self.alloc_vec_call(*op, *element, values, expr.ty, expr.span)?
                    }
                    Target::Function(index) => {
                        let function = &self.program.functions[*index];
                        let mut physical = Vec::with_capacity(values.len());
                        for (position, value) in values.into_iter().enumerate() {
                            if !function
                                .parameter_grades
                                .get(position)
                                .copied()
                                .flatten()
                                .is_some_and(Grade::is_zero)
                            {
                                physical.push(value);
                            }
                        }
                        self.call(*index, physical)?
                    }
                    Target::Foreign(index) => {
                        let function = &self.program.foreign_functions[*index]
                            .as_ref()
                            .expect("checked foreign target");
                        return Err(Diagnostic::new(
                            expr.span,
                            format!(
                                "foreign C function '{}' can only be executed by the native backend (kush build/run); the bounded reference interpreter rejects host FFI instead of guessing its behavior",
                                function.symbol
                            ),
                        ));
                    }
                    Target::DynCall { spec, .. } => {
                        let spec = self.program.dyn_calls[*spec].clone();
                        let first = values.remove(0);
                        let (member, receiver) = match spec.mode {
                            ReceiverMode::Owned => match first {
                                Value::DynObject { member, value } => {
                                    let payload = match Arc::try_unwrap(value) {
                                        Ok(cell) => cell.into_inner().unwrap(),
                                        Err(cell) => cell.lock().unwrap().clone(),
                                    };
                                    self.stats.deallocation();
                                    (member, payload)
                                }
                                other => {
                                    return Err(Diagnostic::new(
                                        expr.span,
                                        format!(
                                            "internal error: dynamic dispatch expected an owned trait object, found {other:?}"
                                        ),
                                    ));
                                }
                            },
                            ReceiverMode::Shared | ReceiverMode::Mutable => {
                                // A whole-object reference or a field place.
                                // The payload is a shared cell, so the method
                                // reads and writes it in place either way.
                                let object = self
                                    .reference_read(&first, Type::Unit)
                                    .ok_or_else(|| {
                                        Diagnostic::new(
                                            expr.span,
                                            "internal error: borrowed dynamic dispatch expected a trait-object reference",
                                        )
                                    })?;
                                let Value::DynObject { member, value } = object else {
                                    return Err(Diagnostic::new(
                                        expr.span,
                                        "internal error: borrowed dynamic dispatch reference does not point at a trait object",
                                    ));
                                };
                                (member, Value::RecordRef(value))
                            }
                        };
                        values.insert(0, receiver);
                        self.call_dyn_member(&spec, member, values, expr.span)?
                    }

                    Target::UnionBorrowCall { spec, .. } => {
                        let spec = self.program.union_calls[*spec].clone();
                        let reference = values.remove(0);
                        let mutable = spec.mode == ReceiverMode::Mutable;
                        // The reference is a whole-object cell or a field
                        // place. The payload is read here and, for an
                        // exclusive call, written back below without dropping
                        // the logically identical old value.
                        let Some(Value::Union { tag, value }) =
                            self.reference_read(&reference, Type::Unit)
                        else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal error: borrowed union dispatch reference does not point at a union",
                            ));
                        };
                        let payload = *value;
                        let (_, _, function) = spec
                            .members
                            .iter()
                            .find(|(member_tag, _, _)| *member_tag == tag)
                            .copied()
                            .ok_or_else(|| {
                                Diagnostic::new(
                                    expr.span,
                                    "internal error: union member tag is not registered for this dispatch",
                                )
                            })?;
                        let payload_cell = Arc::new(Mutex::new(payload));
                        let mut args = vec![Value::RecordRef(payload_cell.clone())];
                        for (index, value) in values.into_iter().enumerate() {
                            if !spec
                                .parameter_grades
                                .get(index)
                                .copied()
                                .flatten()
                                .is_some_and(Grade::is_zero)
                            {
                                args.push(value);
                            }
                        }
                        let result = self.call(function, args)?;
                        if mutable {
                            let updated = match Arc::try_unwrap(payload_cell) {
                                Ok(cell) => cell.into_inner().unwrap(),
                                Err(cell) => cell.lock().unwrap().clone(),
                            };
                            self.reference_swap(
                                &reference,
                                Value::Union {
                                    tag,
                                    value: Box::new(updated),
                                },
                            )?;
                        }
                        result
                    }
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
            _ => unreachable!("expression dispatched to the wrong evaluator helper"),
        };
        Ok(Flow::Value(value))
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
            // Handler arms live in separate non-inlined methods so their
            // locals do not enlarge every recursive `expr` frame.
            ExprKind::HandlerPush {
                operation,
                handler,
                body,
            } => value!(self.handler_push(*operation, handler, body, frame)),
            ExprKind::DynamicPerform {
                operation,
                payload,
                resume,
                ..
            } => value!(self.dynamic_perform(expr, *operation, payload, resume, frame)),
            ExprKind::Constant(n) => Value::Scalar(*n),
            // Only synthesized adapters use this placeholder, and the callee's
            // erased parameter position drops it. It is never observable.
            ExprKind::Erased(_) => Value::Scalar(0),
            ExprKind::FnValue { function, captures } => {
                if captures.is_empty() {
                    Value::Function {
                        function: *function,
                        environment: None,
                    }
                } else {
                    let capture_refs = self.program.functions[*function].capture_refs.clone();
                    let mut values = Vec::with_capacity(captures.len());
                    for (index, capture) in captures.iter().enumerate() {
                        if capture_refs.get(index).copied().unwrap_or(false) {
                            let slot = match &capture.kind {
                                ExprKind::Local(slot)
                                | ExprKind::Peek(slot)
                                | ExprKind::Move(slot) => *slot,
                                _ => {
                                    return Err(Diagnostic::new(
                                        capture.span,
                                        "internal error: by-reference scalar capture is not a local place",
                                    ));
                                }
                            };
                            values.push(self.capture_scalar_reference(slot, frame));
                        } else {
                            values.push(value!(self.expr(capture, frame)));
                        }
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
                let erased: Vec<bool> = match callee.ty {
                    Type::Fn(id) | Type::Once(id) => (0..values.len())
                        .map(|position| self.program.function_types[id].parameter_erased(position))
                        .collect(),
                    _ => Vec::new(),
                };
                let values = values
                    .into_iter()
                    .enumerate()
                    .filter(|(position, _)| erased.get(*position).copied() != Some(true))
                    .map(|(_, value)| value)
                    .collect::<Vec<_>>();
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
                let handlers = self.inheritable_handlers();
                let id = self
                    .task_comm()?
                    .spawn(function, environment, *obligation, handlers)?;
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
                    Coercion::Struct { kept, drops, .. } => {
                        self.apply_struct_coercion(inner, kept, drops, expr.span)?
                    }
                    Coercion::DynBox { member, .. } => {
                        self.stats.allocation();
                        Value::DynObject {
                            member: *member,
                            value: Arc::new(Mutex::new(inner)),
                        }
                    }
                    Coercion::DynUpcast { from, to } => {
                        self.dyn_upcast(*from, *to, inner, expr.span)?
                    }
                    Coercion::Callable {
                        function, capture, ..
                    } => {
                        if capture.is_some() {
                            let environment = self.allocate(Value::Closure {
                                captures: vec![inner],
                            });
                            let Value::Owned(environment) = environment else {
                                unreachable!("closure environment allocation")
                            };
                            Value::Function {
                                function: *function,
                                environment: Some(environment),
                            }
                        } else {
                            Value::Function {
                                function: *function,
                                environment: None,
                            }
                        }
                    }
                }
            }
            ExprKind::DynArrayNew { capacity, .. } => Value::DynArray {
                items: Vec::new(),
                capacity: *capacity,
            },
            ExprKind::DynArrayPush {
                array: array_expr,
                value: value_expr,
                capacity,
                ..
            } => {
                let mut array = value!(self.expr(array_expr, frame));
                let value = value!(self.expr(value_expr, frame));
                self.consume(array_expr, frame);
                self.consume(value_expr, frame);
                let Value::DynArray {
                    items,
                    capacity: actual,
                } = &mut array
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: DynArray.push received a non-array value",
                    ));
                };
                debug_assert_eq!(actual, capacity);
                if items.len() >= *capacity {
                    return Err(Diagnostic::new(
                        expr.span,
                        "panic: DynArray capacity exceeded",
                    ));
                }
                items.push(value);
                array
            }
            ExprKind::DynArrayFill {
                length: length_expr,
                value: value_expr,
                capacity,
                check,
                ..
            } => {
                let length = value!(self.expr(length_expr, frame));
                let value = value!(self.expr(value_expr, frame));
                self.consume(length_expr, frame);
                self.consume(value_expr, frame);
                let length = usize::try_from(length.scalar())
                    .ok()
                    .filter(|length| length <= capacity);
                let Some(length) = length else {
                    return Err(Diagnostic::new(
                        expr.span,
                        if *check {
                            "panic: runtime array length out of range for its capacity"
                        } else {
                            "internal error: a proved runtime array length is out of range"
                        },
                    ));
                };
                Value::DynArray {
                    items: vec![value; length],
                    capacity: *capacity,
                }
            }
            ExprKind::DynArraySet {
                array: array_expr,
                index: index_expr,
                value: value_expr,
                capacity,
                ..
            } => {
                let mut array = value!(self.expr(array_expr, frame));
                let index = value!(self.expr(index_expr, frame));
                let value = value!(self.expr(value_expr, frame));
                self.consume(array_expr, frame);
                self.consume(index_expr, frame);
                self.consume(value_expr, frame);
                let Value::DynArray {
                    items,
                    capacity: actual,
                } = &mut array
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: DynArray.set received a non-array value",
                    ));
                };
                debug_assert_eq!(actual, capacity);
                let position = usize::try_from(index.scalar()).map_err(|_| {
                    Diagnostic::new(expr.span, "panic: DynArray index out of bounds")
                })?;
                let Some(slot) = items.get_mut(position) else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "panic: DynArray index out of bounds",
                    ));
                };
                *slot = value;
                array
            }
            ExprKind::DynArrayPop {
                array: array_expr,
                capacity,
                ..
            } => {
                let mut array = value!(self.expr(array_expr, frame));
                self.consume(array_expr, frame);
                let Value::DynArray {
                    items,
                    capacity: actual,
                } = &mut array
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: DynArray.pop received a non-array value",
                    ));
                };
                debug_assert_eq!(actual, capacity);
                let Some(item) = items.pop() else {
                    return Err(Diagnostic::new(expr.span, "panic: DynArray is empty"));
                };
                Value::Enum {
                    tag: 0,
                    fields: vec![array, item],
                }
            }
            ExprKind::DynArrayEqual {
                left: left_expr,
                right: right_expr,
                element,
                capacity,
                negate,
            } => {
                let left = value!(self.expr(left_expr, frame));
                let right = value!(self.expr(right_expr, frame));
                let (
                    Value::DynArray {
                        items: left_items,
                        capacity: left_capacity,
                    },
                    Value::DynArray {
                        items: right_items,
                        capacity: right_capacity,
                    },
                ) = (&left, &right)
                else {
                    return Err(Diagnostic::new(
                        expr.span,
                        "internal error: DynArray equality received a non-array value",
                    ));
                };
                debug_assert_eq!(*left_capacity, *capacity);
                debug_assert_eq!(*right_capacity, *capacity);
                let equal = left_items.len() == right_items.len()
                    && left_items
                        .iter()
                        .zip(right_items)
                        .all(|(a, b)| comparable_equal(*element, a.scalar(), b.scalar()));
                Value::Scalar(i64::from(equal != *negate))
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
                    Value::PlaceRef { root, steps, .. } => {
                        let pointer = base.ty.ref_pointee().expect("record reference");
                        let pointee = self.program.pointees[pointer];
                        let whole = root.lock().unwrap().clone();
                        let value = self.place_read(whole, &steps).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal error: projected place reference is missing",
                            )
                        })?;
                        (pointee, value)
                    }
                    Value::ElementRef {
                        owner,
                        index,
                        steps,
                        ..
                    } => {
                        let pointer = base.ty.ref_pointee().expect("record reference");
                        let pointee = self.program.pointees[pointer];
                        let element = self.element_value(owner, index).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal ownership error: dangling element reference",
                            )
                        })?;
                        let value = self.place_read(element, &steps).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal error: projected element reference is missing",
                            )
                        })?;
                        (pointee, value)
                    }
                    Value::SliceElementRef { view, index, steps } => {
                        let pointer = base.ty.ref_pointee().expect("record reference");
                        let pointee = self.program.pointees[pointer];
                        let element = self.slice_element(&view, index, expr.span)?;
                        let value = self.place_read(element, &steps).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal error: projected slice element reference is missing",
                            )
                        })?;
                        (pointee, value)
                    }
                    value => (base.ty, value),
                };
                project(
                    &self.program.pointees,
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
                field,
            } => {
                return self.eval_slice(expr, base, start, end, *check, *text, field, frame);
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
                    returned @ (Flow::Return(_) | Flow::Exit(..)) => return Ok(returned),
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
                    returned @ (Flow::Return(_) | Flow::Exit(..)) => return Ok(returned),
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
            ExprKind::Region { body, finish, .. } => {
                let (value, apply) = match self.block(body, frame)? {
                    Flow::Value(value) => (value, true),
                    Flow::Exit(value, apply) => (value, apply),
                    other => return Ok(other),
                };
                match finish {
                    Some(finish) if apply => {
                        let callable = value!(self.expr(finish, frame));
                        self.consume(finish, frame);
                        self.call_value(callable, vec![value])?
                    }
                    _ => value,
                }
            }
            ExprKind::RegionExit {
                value,
                finish,
                cleanup,
            } => {
                let exited = value!(self.expr(value, frame));
                self.consume(value, frame);
                for id in cleanup {
                    self.drop_resource(Some(*id), frame)?;
                }
                return Ok(Flow::Exit(exited, *finish));
            }
            ExprKind::TryExit {
                value,
                input,
                output,
                cleanup,
            } => {
                let Value::Enum { tag, mut fields } = value!(self.expr(value, frame)) else {
                    unreachable!()
                };
                self.consume(value, frame);
                if tag == input.ok_tag {
                    fields.remove(0)
                } else {
                    for id in cleanup {
                        self.drop_resource(Some(*id), frame)?;
                    }
                    return Ok(Flow::Exit(
                        Value::Enum {
                            tag: output.err_tag,
                            fields,
                        },
                        true,
                    ));
                }
            }
            ExprKind::HandlerDepth => Value::Scalar(self.dynamic_handlers.len() as i64),
            ExprKind::HandlerRedirect { depth, body } => {
                let target = value!(self.expr(depth, frame)).scalar() as usize;
                let before = self.dynamic_handlers.len();
                if before > target {
                    self.dynamic_handlers.push(HandlerFrame {
                        operation: usize::MAX,
                        handler: None,
                        redirect: Some(target),
                        consume: true,
                    });
                }
                let flow = self.block(body, frame);
                while self.dynamic_handlers.len() > before {
                    if let Some(HandlerFrame {
                        handler: Some(value),
                        ..
                    }) = self.dynamic_handlers.pop()
                    {
                        self.drop_value(value)?;
                    }
                }
                return flow;
            }
            ExprKind::Suspendable(_) | ExprKind::Suspend { .. } => {
                return Err(Diagnostic::new(
                    expr.span,
                    "internal error: a suspendable body reached the evaluator unlowered",
                ));
            }
            ExprKind::Move(slot) => {
                if let Some(id) = self.program.functions[frame.function].local_resources[*slot] {
                    frame.resources[id] = None;
                }
                self.materialize(frame.locals[*slot].clone())
            }
            ExprKind::Borrow(slot) => self.borrow_local_value(*slot, frame)?,
            ExprKind::InitOwner { slot, value: init } => {
                let value = value!(self.expr(init, frame));
                self.consume(init, frame);
                self.store_initialized_owner(*slot, value, frame)?;
                self.materialize(frame.locals[*slot].clone())
            }
            ExprKind::BorrowInit { slot, value: init } => {
                // Initialize at the operand's source position, then borrow the
                // hidden slot. `value!` propagates panic/return/break/continue
                // exactly as the un-hoisted initializer would.
                let value = value!(self.expr(init, frame));
                self.consume(init, frame);
                self.store_initialized_owner(*slot, value, frame)?;
                self.borrow_local_value(*slot, frame)?
            }
            ExprKind::BorrowPlace(place) => place_value!(self.borrow_place(place, frame)),
            ExprKind::PlaceIndex { .. } => place_value!(self.place_index_reference(expr, frame)),
            ExprKind::BoxNew(..)
            | ExprKind::BoxTake(..)
            | ExprKind::BoxRead(..)
            | ExprKind::BoxWrite(..)
            | ExprKind::BoxReuse { .. }
            | ExprKind::BoxReuseGrow { .. }
            | ExprKind::ArenaNew
            | ExprKind::ArenaNewWith { .. }
            | ExprKind::ArenaAlloc { .. }
            | ExprKind::ArenaTryAlloc { .. }
            | ExprKind::ArenaBoxRead(..)
            | ExprKind::ArenaBoxTake(..)
            | ExprKind::AllocatorNew { .. }
            | ExprKind::AllocatorContextNew { .. }
            | ExprKind::AllocatorContextShare(_)
            | ExprKind::AllocBoxNew { .. }
            | ExprKind::AllocBoxTryNew { .. }
            | ExprKind::AllocBoxRead(..)
            | ExprKind::AllocBoxTake(..)
            | ExprKind::AllocVecNew { .. }
            | ExprKind::BoxTryNew { .. }
            | ExprKind::BoxTryReuse { .. }
            | ExprKind::BytesTryWithCapacity { .. } => {
                return self.expression_allocations(expr, frame);
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
                } else if self.program.owns(arg.ty) {
                    self.drop_value(value)?;
                }
                Value::Scalar(0)
            }
            ExprKind::RefRead(reference_expr) => {
                let reference = value!(self.expr(reference_expr, frame));
                let pointer = reference_expr.ty.ref_pointee().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "internal error: whole-value reference read has no pointee",
                    )
                })?;
                let pointee = self.program.pointees[pointer];
                self.reference_read(&reference, pointee).ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "internal error: whole-value reference read has no inline storage",
                    )
                })?
            }
            ExprKind::DerefWrite(reference_expr, replacement_expr) => {
                let reference = value!(self.expr(reference_expr, frame));
                let replacement = value!(self.expr(replacement_expr, frame));
                self.consume(replacement_expr, frame);
                let pointer = reference_expr.ty.ref_pointee().ok_or_else(|| {
                    Diagnostic::new(
                        expr.span,
                        "internal error: dereference write has no pointee",
                    )
                })?;
                let pointee = self.program.pointees[pointer];
                self.reference_replace(&reference, pointee, replacement)?;
                Value::Scalar(0)
            }
            ExprKind::RefAssign(reference_expr, offset, replacement) => {
                let reference = value!(self.expr(reference_expr, frame));
                let replacement_ty = replacement.ty;
                let replacement = value!(self.expr(replacement, frame));
                let pointer = reference_expr
                    .ty
                    .ref_pointee()
                    .expect("checked record reference");
                let ty = self.program.pointees[pointer];
                let assign = |whole: &mut Value| {
                    assign_project(
                        &self.program.pointees,
                        &self.program.enums,
                        &self.program.unions,
                        &self.program.function_types,
                        ty,
                        whole,
                        *offset,
                        replacement_ty,
                        replacement,
                    )
                };
                match reference {
                    Value::RecordRef(cell) => {
                        let mut whole = cell.lock().unwrap();
                        if !assign(&mut whole) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: record field write has no matching field",
                            ));
                        }
                    }
                    Value::PlaceRef { root, steps, .. } => {
                        let mut whole = root.lock().unwrap().clone();
                        let target =
                            self.place_navigate_mut(&mut whole, &steps).ok_or_else(|| {
                                Diagnostic::new(
                                    expr.span,
                                    "internal error: place field write has no target",
                                )
                            })?;
                        if !assign(target) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: record field write has no matching field",
                            ));
                        }
                        *root.lock().unwrap() = whole;
                    }
                    Value::ElementRef {
                        owner,
                        index,
                        steps,
                        ..
                    } => {
                        let mut element = self.element_value(owner, index).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal ownership error: dangling element field write",
                            )
                        })?;
                        let target =
                            self.place_navigate_mut(&mut element, &steps)
                                .ok_or_else(|| {
                                    Diagnostic::new(
                                        expr.span,
                                        "internal error: element field write has no target",
                                    )
                                })?;
                        if !assign(target) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: record field write has no matching field",
                            ));
                        }
                        let mut vector = self.heap.get(owner).ok_or_else(|| {
                            Diagnostic::new(
                                expr.span,
                                "internal ownership error: dangling element vector",
                            )
                        })?;
                        let Value::Vector { items, .. } = &mut vector else {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: element owner is not a vector",
                            ));
                        };
                        items[index] = element;
                        self.heap.insert(owner, vector);
                    }
                    Value::SliceElementRef { view, index, steps } => {
                        let mut element = self.slice_element(&view, index, expr.span)?;
                        let target =
                            self.place_navigate_mut(&mut element, &steps)
                                .ok_or_else(|| {
                                    Diagnostic::new(
                                        expr.span,
                                        "internal error: slice element field write has no target",
                                    )
                                })?;
                        if !assign(target) {
                            return Err(Diagnostic::new(
                                expr.span,
                                "internal ownership error: record field write has no matching field",
                            ));
                        }
                        self.slice_set(&view, index, element, expr.span)?;
                    }
                    _ => {
                        return Err(Diagnostic::new(
                            expr.span,
                            "internal ownership error: record field write has no record reference",
                        ));
                    }
                }
                Value::Scalar(0)
            }
            ExprKind::StructEq {
                left,
                right,
                negated,
            } => {
                let ty = left.ty;
                let left = value!(self.expr(left, frame));
                let right = value!(self.expr(right, frame));
                let equal = self.struct_value_eq(ty, &left, &right, expr.span)?;
                Value::Scalar(i64::from(equal ^ *negated))
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
                target,
                grow,
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
                return self
                    .vec_map_call(id, functions, *grow, self.program.width(*target), expr.span)
                    .map(Flow::Value);
            }
            ExprKind::Call(..) => return self.expression_call(expr, frame),
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
            ExprKind::Match(input, arms) if input.ty.is_ref() => {
                // A borrowed DynArray match: test a snapshot of the referent,
                // bind element references into its live storage, and never
                // move or drop anything the scrutinee owns.
                let reference = value!(self.expr(input, frame));
                let snapshot = self.reference_read(&reference, Type::Unit).ok_or_else(|| {
                    Diagnostic::new(expr.span, "internal error: dangling borrowed match")
                })?;
                for arm in arms {
                    if !pattern_test(&arm.pattern, &snapshot) {
                        continue;
                    }
                    self.bind_borrowed_dyn(&arm.pattern, &reference, &snapshot, frame);
                    if let Some(guard) = &arm.guard
                        && value!(self.expr(guard, frame)).scalar() == 0
                    {
                        continue;
                    }
                    self.consume(input, frame);
                    let mut slots = std::collections::BTreeSet::new();
                    crate::ownership::pattern_bindings(&arm.pattern, &mut slots);
                    for slot in &slots {
                        self.local_active(*slot, frame);
                    }
                    let result = match self.expr(&arm.body, frame)? {
                        Flow::Value(v) => v,
                        other => return Ok(other),
                    };
                    self.consume(&arm.body, frame);
                    for slot in slots.into_iter().rev() {
                        self.drop_resource(
                            self.program.functions[frame.function].local_resources[slot],
                            frame,
                        )?;
                    }
                    return Ok(Flow::Value(result));
                }
                unreachable!("exhaustiveness checked")
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
    /// Bind a borrowed DynArray pattern. Element names receive references
    /// into the referent's storage (a handle borrow for an owning element, as
    /// for any reference to an owner), the rest receives a `&[T]` view, and
    /// by-value element patterns bind copies of copyable elements.
    fn bind_borrowed_dyn(
        &mut self,
        pattern: &Pattern,
        reference: &Value,
        snapshot: &Value,
        frame: &mut Frame,
    ) {
        let Pattern::DynArray {
            element,
            prefix,
            suffix,
            rest_binding,
            ..
        } = pattern
        else {
            return;
        };
        let Value::DynArray { items, .. } = snapshot else {
            return;
        };
        let view = Value::Slice(Box::new(SliceValue {
            base: Box::new(Value::Scalar(0)),
            start: 0,
            len: items.len(),
            array: None,
            field: Some(Vec::new()),
            reference: Some(Box::new(reference.clone())),
        }));
        let owner_like = matches!(
            element,
            Type::Box(_)
                | Type::Arena
                | Type::ArenaBox(_)
                | Type::Bytes
                | Type::String
                | Type::Vec(_)
                | Type::AllocatorContext
                | Type::AllocBox(_)
                | Type::AllocVec(_)
        );
        let element_reference = |index: usize| -> Value {
            if owner_like {
                match &items[index] {
                    Value::Owned(id) => return Value::Borrowed(*id),
                    Value::Arena { state } => return Value::ArenaRef(state.clone()),
                    Value::ArenaBox { state, slot } => {
                        return Value::ArenaBoxRef {
                            state: state.clone(),
                            slot: *slot,
                        };
                    }
                    Value::AllocatorContext(state) => {
                        return Value::AllocatorContextRef(state.clone());
                    }
                    _ => {}
                }
            }
            Value::SliceElementRef {
                view: Box::new(view.clone()),
                index,
                steps: Vec::new(),
            }
        };
        let end = items.len() - suffix.len();
        let positions = prefix
            .iter()
            .enumerate()
            .chain(suffix.iter().enumerate().map(|(j, p)| (end + j, p)));
        for (index, pattern) in positions {
            match pattern {
                Pattern::Bind(slot) => frame.locals[*slot] = element_reference(index),
                pattern => {
                    pattern_matches(pattern, &items[index], &mut frame.locals);
                }
            }
        }
        if let Some(slot) = rest_binding {
            frame.locals[*slot] = Value::Slice(Box::new(SliceValue {
                base: Box::new(Value::Scalar(0)),
                start: prefix.len(),
                len: end - prefix.len(),
                array: None,
                field: Some(Vec::new()),
                reference: Some(Box::new(reference.clone())),
            }));
        }
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
            Pattern::DynArray {
                prefix,
                suffix,
                rest_binding,
                ..
            } => {
                let Value::DynArray { items, .. } = value else {
                    unreachable!()
                };
                if let Some(slot) = rest_binding {
                    self.local_active(*slot, frame);
                }
                for (pattern, item) in prefix.iter().zip(items) {
                    self.activate_pattern(pattern, item, frame)?;
                }
                let start = items.len() - suffix.len();
                for (pattern, item) in suffix.iter().zip(&items[start..]) {
                    self.activate_pattern(pattern, item, frame)?;
                }
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
        Pattern::Variant { tag, fields, .. } => {
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
        Pattern::DynArray {
            prefix,
            suffix,
            rest,
            ..
        } => {
            let Value::DynArray { items, .. } = value else {
                return false;
            };
            let required = prefix.len() + suffix.len();
            let length_ok = if *rest {
                items.len() >= required
            } else {
                items.len() == required
            };
            length_ok
                && prefix
                    .iter()
                    .zip(items)
                    .all(|(pattern, item)| pattern_test(pattern, item))
                && suffix
                    .iter()
                    .zip(&items[items.len() - suffix.len()..])
                    .all(|(pattern, item)| pattern_test(pattern, item))
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
        Pattern::DynArray {
            capacity,
            prefix,
            suffix,
            rest_binding,
            ..
        } => {
            let Value::DynArray { items, .. } = value else {
                unreachable!()
            };
            for (pattern, item) in prefix.iter().zip(items) {
                pattern_matches(pattern, item, locals);
            }
            let end = items.len() - suffix.len();
            for (pattern, item) in suffix.iter().zip(&items[end..]) {
                pattern_matches(pattern, item, locals);
            }
            if let Some(slot) = rest_binding {
                locals[*slot] = Value::DynArray {
                    items: items[prefix.len()..end].to_vec(),
                    capacity: *capacity,
                };
            }
        }
        _ => {}
    }
    true
}

/// Copy the field at a word offset out of a record value.
/// Compare two one-word DynArray elements with the element type's ordinary
/// equality. Floats compare numerically; integers compare exactly.
fn comparable_equal(element: Type, left: i64, right: i64) -> bool {
    if let Some(kind) = element.int_kind() {
        crate::int::compare(kind, &crate::lexer::Kind::EqEq, left, right)
    } else if let Some(kind) = element.float_kind() {
        crate::float::compare(kind, &crate::lexer::Kind::EqEq, left, right)
    } else {
        left == right
    }
}
/// Walk a record field index path into an evaluated record value.
fn navigate_field<'a>(value: &'a Value, path: &[usize]) -> Option<&'a Value> {
    let mut current = value;
    for index in path {
        let Value::Enum { fields, .. } = current else {
            return None;
        };
        current = fields.get(*index)?;
    }
    Some(current)
}
fn navigate_field_mut<'a>(value: &'a mut Value, path: &[usize]) -> Option<&'a mut Value> {
    let mut current = value;
    for index in path {
        let Value::Enum { fields, .. } = current else {
            return None;
        };
        current = fields.get_mut(*index)?;
    }
    Some(current)
}
/// The direct local at the root of a field projection chain.
/// The temporary-owner initializer at the root of a field projection chain.
fn projection_root_init(expr: &Expr) -> Option<(usize, &Expr)> {
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, _) => current = base,
            ExprKind::InitOwner { slot, value } => return Some((*slot, value)),
            _ => return None,
        }
    }
}
fn projection_root_slot(expr: &Expr) -> Option<usize> {
    let mut current = expr;
    loop {
        match &current.kind {
            ExprKind::Project(base, _) => current = base,
            ExprKind::Peek(slot)
            | ExprKind::Local(slot)
            | ExprKind::Move(slot)
            | ExprKind::InitOwner { slot, .. }
            | ExprKind::BorrowInit { slot, .. } => {
                return Some(*slot);
            }
            _ => return None,
        }
    }
}
fn project(
    pointees: &[Type],
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
    let mut at = enums[id].tag_words();
    for (field, field_ty) in fields.into_iter().zip(&enums[id].variants[0].fields) {
        if at == offset {
            return field;
        }
        at += crate::runtime_types::width(pointees, enums, unions, functions, *field_ty);
    }
    unreachable!("checked field offset")
}
/// Store a checked copyable field through a record reference. `offset` is a
/// word offset from the record tag; nested copyable record paths are handled by
/// recursing instead of flattening or copying the whole owner.
#[allow(clippy::too_many_arguments)]
fn assign_project(
    pointees: &[Type],
    enums: &[crate::runtime_types::Enum],
    unions: &[crate::runtime_types::UnionType],
    functions: &[crate::runtime_types::FunctionType],
    ty: Type,
    value: &mut Value,
    offset: usize,
    replacement_ty: Type,
    replacement: Value,
) -> bool {
    let Value::Enum { fields, .. } = value else {
        return false;
    };
    let id = ty.layout().unwrap();
    let mut at = enums[id].tag_words();
    for (index, field_ty) in enums[id].variants[0].fields.iter().enumerate() {
        let width = crate::runtime_types::width(pointees, enums, unions, functions, *field_ty);
        if at == offset && *field_ty == replacement_ty {
            fields[index] = replacement;
            return true;
        }
        if offset >= at && offset < at + width {
            return assign_project(
                pointees,
                enums,
                unions,
                functions,
                *field_ty,
                &mut fields[index],
                offset - at,
                replacement_ty,
                replacement,
            );
        }
        at += width;
    }
    false
}
