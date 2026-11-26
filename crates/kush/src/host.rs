//! Host operations, shared by the evaluators (FND-EVAL-HOST): the checked
//! host calls (`FS`, `ENV`, `TIME`, `PROC`, `NET`, `OS`) and the reference
//! shims of the `kush_sys_*` stubs `std.sys` imports, on plain bytes and
//! scalars. Each evaluator presents a call's arguments through
//! [`HostArgs`] and turns the result back into its own values.
//!
//! Two calls stay with the evaluators: reads and writes of the standard
//! streams (they go through the evaluator's input and output) and
//! `kush_sys_wait_ready` (it yields to other tasks between polls).

use crate::executable::HostOp;
use crate::{Diagnostic, Span};
use std::{
    collections::{BTreeMap, BTreeSet, VecDeque},
    ffi::OsString,
    fs::{self, OpenOptions},
    io::{self, Read, Write},
    net::{Shutdown, TcpStream, ToSocketAddrs},
    path::PathBuf,
    process::{Command, Stdio},
    sync::{
        Arc, Mutex,
        atomic::{AtomicBool, AtomicU8, Ordering},
    },
    thread,
    time::{Duration, Instant, SystemTime, UNIX_EPOCH},
};

type Result<T> = std::result::Result<T, Diagnostic>;

/// The arguments of one host call, as the evaluator holds them.
pub(crate) trait HostArgs {
    fn scalar(&self, index: usize) -> i64;
    /// The bytes of a borrowed buffer argument.
    fn bytes(&self, index: usize) -> Option<Vec<u8>>;
    /// A buffer argument (owned, or behind a `&mut`) to fill: `(index,
    /// bytes, capacity)`.
    fn take_buffer(&mut self, index: usize) -> Option<(usize, Vec<u8>, usize)>;
    /// The new contents of a buffer argument taken with `take_buffer`.
    fn put_buffer(&mut self, index: usize, data: Vec<u8>);
    /// An owned buffer argument the call consumed (it is freed).
    fn consume_buffer(&mut self, index: usize);
}

/// A successful call's payload: a scalar, or the buffer argument at an
/// index (which `put_buffer` filled).
#[derive(Debug, Clone, Copy, PartialEq)]
pub(crate) enum HostValue {
    Scalar(i64),
    Buffer(usize),
}

/// A call's status (0, or a positive errno) and payload.
pub(crate) fn host_result(status: i64, value: HostValue) -> (i64, HostValue) {
    (status, value)
}

/// Append to a bounded buffer: `Some(EFBIG)` when it does not fit.
pub(crate) fn append_bounded(data: &mut Vec<u8>, capacity: usize, bytes: &[u8]) -> Option<i64> {
    if data.len() > capacity || bytes.len() > capacity - data.len() {
        return Some(27); // EFBIG
    }
    data.extend_from_slice(bytes);
    None
}

pub(crate) fn io_error_code(error: &io::Error) -> i64 {
    // Injected readers/writers may have no platform errno; map those to Linux EIO.
    error
        .raw_os_error()
        .filter(|code| *code > 0)
        .map_or(5, i64::from)
}
pub(crate) fn os_bytes(value: OsString) -> Vec<u8> {
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
pub(crate) fn value_bytes(value: &[u8]) -> OsString {
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
pub(crate) fn path_from_bytes(value: &[u8]) -> PathBuf {
    PathBuf::from(value_bytes(value))
}
/// Split a NUL-separated argument encoding, ignoring empty segments and a
/// trailing NUL exactly like the native subprocess path.
pub(crate) fn split_nul(value: &[u8]) -> Vec<OsString> {
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
pub(crate) fn exit_status_code(status: std::process::ExitStatus) -> i64 {
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
    pub(crate) args: Arc<Vec<Vec<u8>>>,
    pub(crate) environment: Arc<BTreeMap<Vec<u8>, Vec<u8>>>,
    pub(crate) monotonic_origin: Instant,
    /// Files opened by `FS.open`, by handle (STD-FILE). Shared by tasks.
    pub(crate) files: Arc<std::sync::Mutex<FileTable>>,
}
/// The evaluator's open files. Handles are never reused, so a stale handle
/// is always `EBADF` here (natively the descriptor number may be reused,
/// which `std.file.File` being linear prevents).
#[derive(Debug, Default)]
pub(crate) struct FileTable {
    pub(crate) open: BTreeMap<i64, fs::File>,
    /// Directories opened by `std.sys.opendir`, sharing the handle counter.
    pub(crate) dirs: BTreeMap<i64, fs::ReadDir>,
    /// STD-PROC-NET-IN-KUSH: pipe read ends from `kush_sys_pipe`, filled by a
    /// thread copying a spawned child's stdout, so `kush_sys_poll` can wait on
    /// them with a timeout.
    pub(crate) pipes: BTreeMap<i64, Arc<EvalPipe>>,
    /// Pipe write ends; usable only as a spawned child's stdout.
    pub(crate) pipe_writers: BTreeMap<i64, Arc<EvalPipe>>,
    /// Spawned children by pid, until they are reaped.
    pub(crate) children: BTreeMap<i64, std::process::Child>,
    /// Connected sockets from `kush_sys_connect`.
    pub(crate) sockets: BTreeMap<i64, TcpStream>,
    /// Address lists from `kush_sys_resolve`.
    pub(crate) addresses: BTreeMap<i64, Vec<std::net::SocketAddr>>,
    /// The address lists that came from `kush_sys_resolve_udp`, whose
    /// `kush_sys_socket` is a datagram socket.
    pub(crate) datagram_lists: BTreeSet<i64>,
    /// UDP sockets from `kush_sys_socket`, bound to an ephemeral port of
    /// the address's family (Rust's std has no unbound socket).
    pub(crate) datagrams: BTreeMap<i64, std::net::UdpSocket>,
    /// WEB-NET: sockets from `kush_sys_socket` that do not listen yet, with
    /// the address `kush_sys_bind` gave them. Rust's std has no unbound
    /// socket, so `kush_sys_listen` binds and listens in one step.
    pub(crate) unbound: BTreeMap<i64, Option<std::net::SocketAddr>>,
    pub(crate) listeners: BTreeMap<i64, std::net::TcpListener>,
    /// Connections a poll on a listener already accepted, for the next
    /// `kush_sys_accept`.
    pub(crate) accepted: BTreeMap<i64, VecDeque<TcpStream>>,
    pub(crate) next: i64,
}
/// The evaluator's poll(2) on one descriptor (STD-PROC-NET-IN-KUSH,
/// WEB-NET): `(errno, events)`, events 0 on timeout. There is no poll
/// without FFI, so each kind of descriptor is waited on its own way.
pub(crate) fn eval_poll(
    files: &Mutex<FileTable>,
    fd: i64,
    events: i64,
    timeout: i64,
) -> (i64, i64) {
    let code = |result: io::Result<i64>| match result {
        Ok(value) => (0, value),
        Err(error) => (io_error_code(&error), 0),
    };
    let wait = (timeout >= 0).then(|| Duration::from_millis(timeout as u64));
    let table = files.lock().unwrap();
    if timeout < -1 {
        (22, 0)
    } else if table
        .accepted
        .get(&fd)
        .is_some_and(|queue| !queue.is_empty())
    {
        (0, events & 1)
    } else if let Some(listener) = table
        .listeners
        .get(&fd)
        .map(std::net::TcpListener::try_clone)
    {
        drop(table);
        // No poll without FFI: try a nonblocking accept every
        // 2 ms until the timeout, keeping what it accepts.
        let deadline = wait.map(|wait| Instant::now() + wait);
        match listener.and_then(|listener| listener.set_nonblocking(true).map(|()| listener)) {
            Err(error) => code(Err(error)),
            Ok(_) if events & 1 == 0 => (0, 0),
            Ok(listener) => loop {
                match listener.accept() {
                    Ok((stream, _)) => {
                        let _ = stream.set_nonblocking(false);
                        let _ = listener.set_nonblocking(false);
                        files
                            .lock()
                            .unwrap()
                            .accepted
                            .entry(fd)
                            .or_default()
                            .push_back(stream);
                        break (0, 1);
                    }
                    Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                        let now = Instant::now();
                        if deadline.is_some_and(|deadline| now >= deadline) {
                            let _ = listener.set_nonblocking(false);
                            break (0, 0);
                        }
                        let step = Duration::from_millis(2);
                        thread::sleep(deadline.map_or(step, |deadline| step.min(deadline - now)));
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                    Err(error) => {
                        let _ = listener.set_nonblocking(false);
                        break code(Err(error));
                    }
                }
            },
        }
    } else if let Some(pipe) = table.pipes.get(&fd).cloned() {
        drop(table);
        if events & 1 == 0 || !pipe.wait(wait) {
            (0, 0)
        } else {
            let state = pipe.state.lock().unwrap();
            let ended = state.data.is_empty() && state.error.is_none();
            (0, if ended { 1 | 16 } else { 1 })
        }
    } else if let Some(socket) = table.sockets.get(&fd).map(TcpStream::try_clone) {
        drop(table);
        // Writes block in the evaluator, so a socket is always
        // writable; readability is a peek with a read timeout.
        match socket {
            Err(error) => code(Err(error)),
            Ok(_) if events & 4 != 0 => (0, 4),
            Ok(_) if events & 1 == 0 => (0, 0),
            Ok(socket) => {
                let armed = match wait {
                    Some(wait) if wait.is_zero() => socket.set_nonblocking(true),
                    wait => socket.set_read_timeout(wait),
                };
                let peeked = armed.and_then(|()| socket.peek(&mut [0u8; 1]));
                let _ = socket.set_nonblocking(false);
                let _ = socket.set_read_timeout(None);
                match peeked {
                    Ok(0) => (0, 1 | 16),
                    Ok(_) => (0, 1),
                    Err(error)
                        if matches!(
                            error.kind(),
                            io::ErrorKind::WouldBlock | io::ErrorKind::TimedOut
                        ) =>
                    {
                        (0, 0)
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => (4, 0),
                    // The read that follows reports the error.
                    Err(_) => (0, 1 | 8),
                }
            }
        }
    } else if table.open.contains_key(&fd) || (0..=2).contains(&fd) {
        (0, events & 5)
    } else if table.unbound.contains_key(&fd) {
        (0, 4 & events)
    } else {
        (9, 0)
    }
}
impl FileTable {
    fn handle(&mut self) -> i64 {
        self.next = self.next.max(2) + 1;
        self.next
    }
}
/// A pipe in the reference evaluator. It reaches end of file once its write
/// end is closed and every child writing to it has closed its stdout.
#[derive(Debug, Default)]
pub(crate) struct EvalPipe {
    state: Mutex<PipeState>,
    ready: std::sync::Condvar,
}
#[derive(Debug, Default)]
pub(crate) struct PipeState {
    data: VecDeque<u8>,
    /// Copy threads still reading a child's stdout into `data`.
    writers: usize,
    /// The write handle was closed.
    closed: bool,
    error: Option<i64>,
}
impl EvalPipe {
    /// Wait until bytes, an error or end of file are there, up to `timeout`
    /// (forever when `None`). Whether anything is.
    fn wait(&self, timeout: Option<Duration>) -> bool {
        let ready = |state: &PipeState| {
            !state.data.is_empty() || state.error.is_some() || (state.closed && state.writers == 0)
        };
        let state = self.state.lock().unwrap();
        match timeout {
            None => ready(&self.ready.wait_while(state, |state| !ready(state)).unwrap()),
            Some(timeout) => {
                let (state, _) = self
                    .ready
                    .wait_timeout_while(state, timeout, |state| !ready(state))
                    .unwrap();
                ready(&state)
            }
        }
    }
    /// One blocking read, like read(2) on a pipe: 0 at end of file.
    fn read(&self, target: &mut [u8]) -> io::Result<usize> {
        if target.is_empty() {
            return Ok(0);
        }
        self.wait(None);
        let mut state = self.state.lock().unwrap();
        if state.data.is_empty() {
            return match state.error {
                Some(code) => Err(io::Error::from_raw_os_error(code as i32)),
                None => Ok(0),
            };
        }
        let count = target.len().min(state.data.len());
        for (slot, byte) in target.iter_mut().zip(state.data.drain(..count)) {
            *slot = byte;
        }
        Ok(count)
    }
    /// Copy `source` into the pipe until it ends.
    fn feed(self: Arc<Self>, mut source: impl Read + Send + 'static) {
        self.state.lock().unwrap().writers += 1;
        thread::spawn(move || {
            let mut chunk = [0u8; 4096];
            loop {
                match source.read(&mut chunk) {
                    Ok(0) => break,
                    Ok(count) => {
                        self.state.lock().unwrap().data.extend(&chunk[..count]);
                        self.ready.notify_all();
                    }
                    Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                    Err(error) => {
                        self.state.lock().unwrap().error = Some(io_error_code(&error));
                        break;
                    }
                }
            }
            self.state.lock().unwrap().writers -= 1;
            self.ready.notify_all();
        });
    }
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
            files: Arc::default(),
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
            files: Arc::default(),
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
            files: Arc::default(),
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

/// The reference shims of the `kush_sys_*` stubs that `std.sys` imports
/// (EVAL-FOREIGN-SHIMS), keyed by symbol like Miri's foreign-function
/// shims. Descriptors live in the same never-reused table as `FS.open`, so
/// a stale descriptor is `EBADF` here. The standard streams and
/// `kush_sys_wait_ready` are the evaluator's (see the module documentation).
pub(crate) fn sys_call(
    system: &Host,
    symbol: &str,
    args: &mut dyn HostArgs,
    fuel: &mut usize,
    span: Span,
) -> Result<(i64, HostValue)> {
    use std::os::unix::fs::{DirBuilderExt, FileExt, MetadataExt, OpenOptionsExt};
    *fuel = fuel
        .checked_sub(1)
        .ok_or_else(|| Diagnostic::new(span, "reference host computation budget exhausted"))?;
    let internal = || Diagnostic::new(span, format!("internal error: bad arguments to {symbol}"));
    let code = |result: io::Result<i64>| match result {
        Ok(value) => (0, value),
        Err(error) => (io_error_code(&error), 0),
    };
    // A path with a NUL byte cannot reach the OS: EINVAL, like the stub.
    let path = |args: &dyn HostArgs, index: usize| -> Result<io::Result<PathBuf>> {
        let bytes = args.bytes(index).ok_or_else(internal)?;
        Ok(if bytes.contains(&0) {
            Err(io::Error::from_raw_os_error(22))
        } else {
            Ok(path_from_bytes(&bytes))
        })
    };
    let files = Arc::clone(&system.files);
    let with_file = |fd: i64, f: &dyn Fn(&fs::File) -> io::Result<i64>| {
        match files.lock().unwrap().open.get(&fd) {
            None => (9, 0), // EBADF
            Some(file) => code(f(file)),
        }
    };
    // One read from a pipe or socket, without holding the table while
    // it blocks; `None` for any other descriptor.
    let stream_read = |fd: i64, target: &mut [u8]| -> Option<io::Result<usize>> {
        let table = files.lock().unwrap();
        if let Some(pipe) = table.pipes.get(&fd).cloned() {
            drop(table);
            return Some(pipe.read(target));
        }
        let socket = table.sockets.get(&fd).map(TcpStream::try_clone);
        drop(table);
        socket.map(|socket| socket.and_then(|mut socket| socket.read(target)))
    };
    if symbol == "kush_sys_getrandom" {
        // Like the stub: fill spare capacity, free the buffer on failure.
        let length = args.scalar(1);
        let (id, mut data, capacity) = args.take_buffer(0).ok_or_else(internal)?;
        let start = data.len();
        let status = if length < 0 {
            22
        } else if length as u64 > (capacity - start) as u64 {
            27 // EFBIG
        } else {
            data.resize(start + length as usize, 0);
            match fs::File::open("/dev/urandom")
                .and_then(|mut source| io::Read::read_exact(&mut source, &mut data[start..]))
            {
                Ok(()) => 0,
                Err(error) => io_error_code(&error),
            }
        };
        if status != 0 {
            args.consume_buffer(id);
            return Ok(host_result(status, HostValue::Scalar(0)));
        }
        args.put_buffer(id, data);
        return Ok(host_result(0, HostValue::Buffer(id)));
    }
    let (status, value) = match symbol {
        // The evaluator runs every intrinsic in software, so it reports
        // every feature unless KUSH_CPU_DISABLE clears it, like the stub.
        "kush_sys_cpu_features" => {
            let disabled = std::env::var("KUSH_CPU_DISABLE").unwrap_or_default();
            let mut bits = 15;
            for (name, bit) in [("ssse3", 1), ("sse41", 2), ("avx2", 4), ("sha", 8)] {
                if disabled.split(',').any(|item| item == name) {
                    bits &= !bit;
                }
            }
            (0, bits)
        }
        "kush_sys_stdin" => (0, 0),
        "kush_sys_openat" => {
            let (flags, mode) = (args.scalar(1), args.scalar(2));
            match path(args, 0)? {
                Err(error) => code(Err(error)),
                Ok(path) => {
                    let mut options = OpenOptions::new();
                    match flags & 3 {
                        0 => options.read(true),
                        1 => options.write(true),
                        _ => options.read(true).write(true),
                    };
                    options
                        .create(flags & 64 != 0)
                        .create_new(flags & 64 != 0 && flags & 128 != 0)
                        .truncate(flags & 512 != 0)
                        .append(flags & 1024 != 0)
                        .custom_flags((flags & !(3 | 64 | 128 | 512 | 1024)) as i32)
                        .mode(mode as u32);
                    match options.open(path) {
                        Ok(file) => {
                            let mut table = system.files.lock().unwrap();
                            table.next = table.next.max(2) + 1;
                            let handle = table.next;
                            table.open.insert(handle, file);
                            (0, handle)
                        }
                        Err(error) => code(Err(error)),
                    }
                }
            }
        }
        "kush_sys_close" => {
            let fd = args.scalar(0);
            let mut table = system.files.lock().unwrap();
            if let Some(writer) = table.pipe_writers.remove(&fd) {
                writer.state.lock().unwrap().closed = true;
                writer.ready.notify_all();
                (0, 0)
            } else if table.open.remove(&fd).is_some()
                || table.pipes.remove(&fd).is_some()
                || table.sockets.remove(&fd).is_some()
                || table.datagrams.remove(&fd).is_some()
                || table.unbound.remove(&fd).is_some()
                || table.listeners.remove(&fd).is_some()
            {
                table.accepted.remove(&fd);
                (0, 0)
            } else {
                (9, 0)
            }
        }
        "kush_sys_fsync" => with_file(args.scalar(0), &|file| file.sync_all().map(|()| 0)),
        "kush_sys_ftruncate" => {
            let length = args.scalar(1);
            with_file(args.scalar(0), &|file| {
                if length < 0 {
                    return Err(io::Error::from_raw_os_error(22));
                }
                file.set_len(length as u64).map(|()| 0)
            })
        }
        "kush_sys_fstat_size" => with_file(args.scalar(0), &|file| {
            file.metadata().map(|m| m.len().min(i64::MAX as u64) as i64)
        }),
        "kush_sys_write" => {
            let data = args.bytes(1).ok_or_else(internal)?;
            let (start, offset) = (args.scalar(2), args.scalar(3));
            with_file(args.scalar(0), &|file| {
                if start < 0 || start as usize > data.len() {
                    return Err(io::Error::from_raw_os_error(22));
                }
                let tail = &data[start as usize..];
                let written = if offset < 0 {
                    io::Write::write(&mut &*file, tail)
                } else {
                    file.write_at(tail, offset as u64)
                };
                written.map(|count| count as i64)
            })
        }
        "kush_sys_read" => {
            // Like the stub: append into spare capacity, retry EINTR,
            // free the buffer on failure.
            let (fd, length, offset) = (args.scalar(0), args.scalar(2), args.scalar(3));
            let (id, mut data, capacity) = args.take_buffer(1).ok_or_else(internal)?;
            let start = data.len();
            let status = if length < 0 {
                22
            } else if length as u64 > (capacity - start) as u64 {
                27 // EFBIG
            } else {
                data.resize(start + length as usize, 0);
                let streamed = if offset < 0 {
                    stream_read(fd, &mut data[start..])
                } else {
                    None
                };
                let table = system.files.lock().unwrap();
                let (status, received) = match (streamed, table.open.get(&fd)) {
                    (Some(Ok(count)), _) => (0, count),
                    (Some(Err(error)), _) => (io_error_code(&error), 0),
                    (None, None) => (9, 0), // EBADF
                    (None, Some(file)) => loop {
                        let target = &mut data[start..];
                        let result = if offset < 0 {
                            io::Read::read(&mut &*file, target)
                        } else {
                            file.read_at(target, offset as u64)
                        };
                        match result {
                            Ok(count) => break (0, count),
                            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                            Err(error) => break (io_error_code(&error), 0),
                        }
                    },
                };
                data.truncate(start + received);
                status
            };
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            return Ok(host_result(0, HostValue::Buffer(id)));
        }
        "kush_sys_probe" => match stream_read(args.scalar(0), &mut [0u8; 1]) {
            Some(result) => code(result.map(|count| count as i64)),
            None => with_file(args.scalar(0), &|file| {
                let mut probe = [0u8; 1];
                loop {
                    match io::Read::read(&mut &*file, &mut probe) {
                        Ok(count) => break Ok(count as i64),
                        Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                        Err(error) => break Err(error),
                    }
                }
            }),
        },
        "kush_sys_opendir" => match path(args, 0)? {
            Err(error) => code(Err(error)),
            Ok(path) => match fs::read_dir(path) {
                Ok(entries) => {
                    let mut table = system.files.lock().unwrap();
                    table.next = table.next.max(2) + 1;
                    let handle = table.next;
                    table.dirs.insert(handle, entries);
                    (0, handle)
                }
                Err(error) => code(Err(error)),
            },
        },
        "kush_sys_closedir" => match system.files.lock().unwrap().dirs.remove(&args.scalar(0)) {
            Some(_) => (0, 0),
            None => (9, 0),
        },
        "kush_sys_readdir" => {
            // Like the stub: append "name\n" (std's read_dir already
            // skips "." and ".."), EFBIG and free when it does not fit.
            let (id, mut data, capacity) = args.take_buffer(1).ok_or_else(internal)?;
            let next = match system.files.lock().unwrap().dirs.get_mut(&args.scalar(0)) {
                None => Err(9),
                Some(entries) => match entries.next() {
                    None => Ok(None),
                    Some(Ok(entry)) => Ok(Some(os_bytes(entry.file_name()))),
                    Some(Err(error)) => Err(io_error_code(&error)),
                },
            };
            let status = match next {
                Err(status) => status,
                Ok(None) => 0,
                Ok(Some(mut name)) => {
                    name.push(b'\n');
                    append_bounded(&mut data, capacity, &name).unwrap_or(0)
                }
            };
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            return Ok(host_result(0, HostValue::Buffer(id)));
        }
        "kush_sys_argc" => (0, system.args.len() as i64),
        "kush_sys_environ_count" => (0, system.environment.len() as i64),
        "kush_sys_argv" | "kush_sys_getenv" | "kush_sys_strerror" => {
            // Append a host string to the owned buffer: the injected
            // argv/environment, or the OS message without Rust's suffix.
            let (id, mut data, capacity) = args.take_buffer(1).ok_or_else(internal)?;
            let text = match symbol {
                "kush_sys_argv" => usize::try_from(args.scalar(0))
                    .ok()
                    .and_then(|index| system.args.get(index))
                    .cloned()
                    .ok_or(2),
                "kush_sys_getenv" => {
                    let name = args.bytes(0).ok_or_else(internal)?;
                    if name.contains(&0) {
                        Err(22)
                    } else {
                        system.var(&name).map(<[u8]>::to_vec).ok_or(2)
                    }
                }
                _ => {
                    let code = args.scalar(0);
                    if (0..=4095).contains(&code) {
                        let mut text = io::Error::from_raw_os_error(code as i32).to_string();
                        if let Some(at) = text.rfind(" (os error ") {
                            text.truncate(at);
                        }
                        Ok(text.into_bytes())
                    } else {
                        Err(22)
                    }
                }
            };
            let status = match text {
                Err(status) => status,
                Ok(text) => append_bounded(&mut data, capacity, &text).unwrap_or(0),
            };
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            return Ok(host_result(0, HostValue::Buffer(id)));
        }
        "kush_sys_clock_gettime" => match (args.scalar(0), args.scalar(1)) {
            (0, 0) => {
                let seconds = match SystemTime::now().duration_since(UNIX_EPOCH) {
                    Ok(duration) => i64::try_from(duration.as_secs()).unwrap_or(i64::MAX),
                    Err(error) => -i64::try_from(error.duration().as_secs()).unwrap_or(i64::MAX),
                };
                (0, seconds)
            }
            (0, 1) => match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(duration) => match i64::try_from(duration.as_nanos()) {
                    Ok(nanos) => (0, nanos),
                    Err(_) => (75, 0), // EOVERFLOW
                },
                Err(_) => (75, 0),
            },
            (1, 0) => (0, system.monotonic_ns() / 1_000_000_000),
            (1, 1) => (0, system.monotonic_ns()),
            (0, 2) => match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(duration) => (0, i64::try_from(duration.as_millis()).unwrap_or(i64::MAX)),
                Err(_) => (75, 0),
            },
            (1, 2) => (0, system.monotonic_ns() / 1_000_000),
            _ => (22, 0),
        },
        "kush_sys_nanosleep" => {
            let milliseconds = args.scalar(0);
            if milliseconds < 0 {
                (22, 0)
            } else {
                thread::sleep(Duration::from_millis(milliseconds as u64));
                (0, 0)
            }
        }
        "kush_sys_unlink" | "kush_sys_rmdir" => match path(args, 0)? {
            Err(error) => code(Err(error)),
            Ok(path) if symbol == "kush_sys_unlink" => code(fs::remove_file(path).map(|()| 0)),
            Ok(path) => code(fs::remove_dir(path).map(|()| 0)),
        },
        "kush_sys_mkdir" => {
            let mode = args.scalar(1) as u32;
            match path(args, 0)? {
                Err(error) => code(Err(error)),
                Ok(path) => code(fs::DirBuilder::new().mode(mode).create(path).map(|()| 0)),
            }
        }
        "kush_sys_rename" => match (path(args, 0)?, path(args, 1)?) {
            (Ok(from), Ok(to)) => code(fs::rename(from, to).map(|()| 0)),
            (Err(error), _) | (_, Err(error)) => code(Err(error)),
        },
        "kush_sys_pipe" => {
            let pipe = Arc::new(EvalPipe::default());
            let mut table = system.files.lock().unwrap();
            let reader = table.handle();
            let writer = table.handle();
            table.pipes.insert(reader, Arc::clone(&pipe));
            table.pipe_writers.insert(writer, pipe);
            (0, reader + (writer << 32))
        }
        "kush_sys_spawn" => {
            let program = args.bytes(0).ok_or_else(internal)?;
            let arguments = args.bytes(1).ok_or_else(internal)?;
            let target = system
                .files
                .lock()
                .unwrap()
                .pipe_writers
                .get(&args.scalar(2))
                .cloned();
            match target {
                None => (9, 0),
                Some(_) if program.is_empty() || program.contains(&0) => (22, 0),
                Some(pipe) => {
                    let spawned = Command::new(value_bytes(&program))
                        .args(split_nul(&arguments))
                        .stdin(Stdio::null())
                        .stdout(Stdio::piped())
                        .stderr(Stdio::null())
                        .spawn();
                    match spawned {
                        Err(error) => (io_error_code(&error), 0),
                        Ok(mut child) => {
                            pipe.feed(child.stdout.take().expect("piped stdout"));
                            let pid = i64::from(child.id());
                            system.files.lock().unwrap().children.insert(pid, child);
                            (0, pid)
                        }
                    }
                }
            }
        }
        "kush_sys_wait" => {
            use std::os::unix::process::ExitStatusExt;
            let (pid, block) = (args.scalar(0), args.scalar(1) != 0);
            let child = system.files.lock().unwrap().children.remove(&pid);
            match child {
                None => (10, 0), // ECHILD
                Some(mut child) => {
                    let status = if block {
                        child.wait().map(Some)
                    } else {
                        child.try_wait()
                    };
                    match status {
                        Ok(None) => {
                            system.files.lock().unwrap().children.insert(pid, child);
                            (0, -1)
                        }
                        Ok(Some(status)) => match (status.code(), status.signal()) {
                            (Some(code), _) => (0, i64::from(code)),
                            (None, Some(signal)) => (0, 128 + i64::from(signal)),
                            (None, None) => (5, 0),
                        },
                        Err(error) => {
                            system.files.lock().unwrap().children.insert(pid, child);
                            code(Err(error))
                        }
                    }
                }
            }
        }
        "kush_sys_kill" => {
            // Only SIGKILL, which is all std.proc sends.
            let (pid, signal) = (args.scalar(0), args.scalar(1));
            match system.files.lock().unwrap().children.get_mut(&pid) {
                None => (3, 0), // ESRCH
                Some(_) if signal != 9 => (22, 0),
                Some(child) => code(child.kill().map(|()| 0)),
            }
        }
        "kush_sys_poll" => {
            let (fd, events, timeout) = (args.scalar(0), args.scalar(1), args.scalar(2));
            eval_poll(&system.files, fd, events, timeout)
        }
        "kush_sys_wait_ready" => return Err(internal()),
        "kush_sys_connect_start" => {
            let (list, index) = (args.scalar(0), args.scalar(1));
            let address = system
                .files
                .lock()
                .unwrap()
                .addresses
                .get(&list)
                .map(|addresses| {
                    usize::try_from(index)
                        .ok()
                        .and_then(|i| addresses.get(i).copied())
                });
            match address {
                None => (9, 0),
                Some(None) => (2, 0),
                // The evaluator connects at once; connect_finish only
                // reports success.
                Some(Some(address)) => match TcpStream::connect(address) {
                    Ok(socket) => {
                        let mut table = system.files.lock().unwrap();
                        let handle = table.handle();
                        table.sockets.insert(handle, socket);
                        (0, handle)
                    }
                    Err(error) => code(Err(error)),
                },
            }
        }
        "kush_sys_connect_finish" => {
            if system
                .files
                .lock()
                .unwrap()
                .sockets
                .contains_key(&args.scalar(0))
            {
                (0, 0)
            } else {
                (9, 0)
            }
        }
        "kush_sys_resolve" | "kush_sys_resolve_udp" | "kush_sys_resolve_udp6" => {
            let host = args.bytes(0).ok_or_else(internal)?;
            let port = args.scalar(1);
            let resolved = match std::str::from_utf8(&host) {
                _ if !(0..=65535).contains(&port) || host.contains(&0) => Err(22),
                Err(_) => Err(22),
                Ok(host) => match (host, port as u16).to_socket_addrs() {
                    // IPv6 only, like getaddrinfo with AF_INET6 and no
                    // AI_V4MAPPED: nothing left is EINVAL, as natively.
                    Ok(addresses) if symbol == "kush_sys_resolve_udp6" => Some(
                        addresses
                            .filter(std::net::SocketAddr::is_ipv6)
                            .collect::<Vec<_>>(),
                    )
                    .filter(|addresses| !addresses.is_empty())
                    .ok_or(22),
                    Ok(addresses) => Ok(addresses.collect::<Vec<_>>()),
                    Err(error) => Err(error
                        .raw_os_error()
                        .filter(|code| *code > 0)
                        .map_or(22, i64::from)),
                },
            };
            match resolved {
                Err(status) => (status, 0),
                Ok(addresses) => {
                    let mut table = system.files.lock().unwrap();
                    let handle = table.handle();
                    table.addresses.insert(handle, addresses);
                    if symbol != "kush_sys_resolve" {
                        table.datagram_lists.insert(handle);
                    }
                    (0, handle)
                }
            }
        }
        "kush_sys_resolve_free" => {
            let mut table = system.files.lock().unwrap();
            table.addresses.remove(&args.scalar(0));
            table.datagram_lists.remove(&args.scalar(0));
            (0, 0)
        }
        "kush_sys_connect" => {
            let (list, index, timeout) = (args.scalar(0), args.scalar(1), args.scalar(2));
            let address = system
                .files
                .lock()
                .unwrap()
                .addresses
                .get(&list)
                .map(|addresses| {
                    usize::try_from(index)
                        .ok()
                        .and_then(|i| addresses.get(i).copied())
                });
            match address {
                None => (9, 0),
                Some(None) => (2, 0), // ENOENT: past the end
                Some(Some(_)) if timeout < -1 => (22, 0),
                Some(Some(address)) => {
                    let connected = if timeout < 0 {
                        TcpStream::connect(address)
                    } else {
                        TcpStream::connect_timeout(
                            &address,
                            Duration::from_millis(timeout.max(1) as u64),
                        )
                    };
                    match connected {
                        Ok(socket) => {
                            let mut table = system.files.lock().unwrap();
                            let handle = table.handle();
                            table.sockets.insert(handle, socket);
                            (0, handle)
                        }
                        Err(error) if error.kind() == io::ErrorKind::TimedOut => (110, 0),
                        Err(error) => code(Err(error)),
                    }
                }
            }
        }
        "kush_sys_send" => {
            let data = args.bytes(1).ok_or_else(internal)?;
            let start = args.scalar(2);
            let socket = system
                .files
                .lock()
                .unwrap()
                .sockets
                .get(&args.scalar(0))
                .map(TcpStream::try_clone);
            match socket {
                None => (9, 0),
                Some(_) if start < 0 || start as usize > data.len() => (22, 0),
                Some(socket) => code(
                    socket
                        .and_then(|mut socket| socket.write(&data[start as usize..]))
                        .map(|count| count as i64),
                ),
            }
        }
        "kush_sys_shutdown" => {
            let how = match args.scalar(1) {
                0 => Some(Shutdown::Read),
                1 => Some(Shutdown::Write),
                2 => Some(Shutdown::Both),
                _ => None,
            };
            match (
                system.files.lock().unwrap().sockets.get(&args.scalar(0)),
                how,
            ) {
                (_, None) => (22, 0),
                (None, _) => (9, 0),
                (Some(socket), Some(how)) => code(socket.shutdown(how).map(|()| 0)),
            }
        }
        "kush_sys_socket" => {
            let (list, index) = (args.scalar(0), args.scalar(1));
            let mut table = system.files.lock().unwrap();
            match table.addresses.get(&list).map(|addresses| {
                usize::try_from(index)
                    .ok()
                    .and_then(|i| addresses.get(i).copied())
            }) {
                None => (9, 0),
                Some(None) => (2, 0),
                Some(Some(address)) if table.datagram_lists.contains(&list) => {
                    let local: std::net::SocketAddr = if address.is_ipv4() {
                        (std::net::Ipv4Addr::UNSPECIFIED, 0).into()
                    } else {
                        (std::net::Ipv6Addr::UNSPECIFIED, 0).into()
                    };
                    match std::net::UdpSocket::bind(local) {
                        Ok(socket) => {
                            let handle = table.handle();
                            table.datagrams.insert(handle, socket);
                            (0, handle)
                        }
                        Err(error) => code(Err(error)),
                    }
                }
                Some(Some(_)) => {
                    let handle = table.handle();
                    table.unbound.insert(handle, None);
                    (0, handle)
                }
            }
        }
        "kush_sys_address_text" => {
            // Append the address's IP as text to the owned buffer, which
            // is freed on failure, like kush_sys_strerror.
            let (id, mut data, capacity) = args.take_buffer(2).ok_or_else(internal)?;
            let (list, index) = (args.scalar(0), args.scalar(1));
            let address = system
                .files
                .lock()
                .unwrap()
                .addresses
                .get(&list)
                .map(|addresses| {
                    usize::try_from(index)
                        .ok()
                        .and_then(|i| addresses.get(i).copied())
                });
            let status = match address {
                None => 9,
                Some(None) => 2,
                Some(Some(address)) => {
                    append_bounded(&mut data, capacity, address.ip().to_string().as_bytes())
                        .unwrap_or(0)
                }
            };
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            return Ok(host_result(0, HostValue::Buffer(id)));
        }
        "kush_sys_connect_to" => {
            let (fd, list, index) = (args.scalar(0), args.scalar(1), args.scalar(2));
            let table = system.files.lock().unwrap();
            let address = table.addresses.get(&list).map(|addresses| {
                usize::try_from(index)
                    .ok()
                    .and_then(|i| addresses.get(i).copied())
            });
            match (table.datagrams.get(&fd), address) {
                (_, None) => (9, 0),
                (_, Some(None)) => (2, 0),
                (Some(socket), Some(Some(address))) => code(socket.connect(address).map(|()| 0)),
                // Rust's std cannot connect an unbound TCP socket.
                (None, _) if table.unbound.contains_key(&fd) => (95, 0), // EOPNOTSUPP
                (None, _) => (9, 0),
            }
        }
        "kush_sys_local_address" => {
            let (id, mut data, capacity) = args.take_buffer(1).ok_or_else(internal)?;
            let fd = args.scalar(0);
            let local = {
                let table = system.files.lock().unwrap();
                if let Some(socket) = table.datagrams.get(&fd) {
                    Some(socket.local_addr())
                } else if let Some(socket) = table.sockets.get(&fd) {
                    Some(socket.local_addr())
                } else {
                    table
                        .listeners
                        .get(&fd)
                        .map(std::net::TcpListener::local_addr)
                }
            };
            let status = match local {
                None => 9,
                Some(Err(error)) => io_error_code(&error),
                Some(Ok(address)) => {
                    append_bounded(&mut data, capacity, address.ip().to_string().as_bytes())
                        .unwrap_or(0)
                }
            };
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            return Ok(host_result(0, HostValue::Buffer(id)));
        }
        "kush_sys_sendto" => {
            let data = args.bytes(1).ok_or_else(internal)?;
            let (fd, list, index) = (args.scalar(0), args.scalar(2), args.scalar(3));
            let table = system.files.lock().unwrap();
            let address = table.addresses.get(&list).map(|addresses| {
                usize::try_from(index)
                    .ok()
                    .and_then(|i| addresses.get(i).copied())
            });
            match (table.datagrams.get(&fd), address) {
                (None, _) | (_, None) => (9, 0),
                (_, Some(None)) => (2, 0),
                (Some(socket), Some(Some(address))) => {
                    code(socket.send_to(&data, address).map(|count| count as i64))
                }
            }
        }
        "kush_sys_setsockopt" => {
            let (fd, level, name, value) = (
                args.scalar(0),
                args.scalar(1),
                args.scalar(2),
                args.scalar(3),
            );
            let table = system.files.lock().unwrap();
            match (level, name) {
                // SO_REUSEADDR is Rust's default for listeners; it cannot
                // set SO_REUSEPORT, so the evaluator ignores it (a second
                // listener on the same port is EADDRINUSE here).
                (1, 2 | 15)
                    if table.unbound.contains_key(&fd) || table.listeners.contains_key(&fd) =>
                {
                    (0, 0)
                }
                (6, 1) => match table.sockets.get(&fd) {
                    Some(socket) => code(socket.set_nodelay(value != 0).map(|()| 0)),
                    None => (9, 0),
                },
                // SO_BROADCAST on a UDP socket.
                (1, 6) if table.datagrams.contains_key(&fd) => {
                    code(table.datagrams[&fd].set_broadcast(value != 0).map(|()| 0))
                }
                _ if table.unbound.contains_key(&fd)
                    || table.sockets.contains_key(&fd)
                    || table.datagrams.contains_key(&fd)
                    || table.listeners.contains_key(&fd) =>
                {
                    (92, 0) // ENOPROTOOPT
                }
                _ => (9, 0),
            }
        }
        "kush_sys_bind" => {
            let (fd, list, index) = (args.scalar(0), args.scalar(1), args.scalar(2));
            let mut table = system.files.lock().unwrap();
            let address = table.addresses.get(&list).map(|addresses| {
                usize::try_from(index)
                    .ok()
                    .and_then(|i| addresses.get(i).copied())
            });
            match (address, table.unbound.get_mut(&fd)) {
                (_, None) => (9, 0),
                (None, _) => (9, 0),
                (Some(None), _) => (2, 0),
                (Some(Some(_)), Some(Some(_))) => (22, 0), // already bound
                (Some(Some(address)), Some(slot)) => {
                    *slot = Some(address);
                    (0, 0)
                }
            }
        }
        "kush_sys_listen" => {
            let fd = args.scalar(0);
            let mut table = system.files.lock().unwrap();
            match table.unbound.get(&fd).copied() {
                None => (
                    if table.listeners.contains_key(&fd) {
                        0
                    } else {
                        9
                    },
                    0,
                ),
                Some(None) => (22, 0),
                Some(Some(address)) => match std::net::TcpListener::bind(address) {
                    Ok(listener) => {
                        table.unbound.remove(&fd);
                        table.listeners.insert(fd, listener);
                        (0, 0)
                    }
                    Err(error) => code(Err(error)),
                },
            }
        }
        "kush_sys_accept" => {
            let fd = args.scalar(0);
            let mut table = system.files.lock().unwrap();
            let queued = table.accepted.get_mut(&fd).and_then(VecDeque::pop_front);
            let listener = table
                .listeners
                .get(&fd)
                .map(std::net::TcpListener::try_clone);
            drop(table);
            let accepted = match queued {
                Some(stream) => Some(Ok(stream)),
                // The listener is nonblocking, as natively: EAGAIN when
                // nothing is queued.
                None => listener.map(|listener| {
                    listener.and_then(|listener| {
                        listener.set_nonblocking(true)?;
                        let accepted = loop {
                            match listener.accept() {
                                Ok((stream, _)) => {
                                    break stream.set_nonblocking(false).map(|()| stream);
                                }
                                Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                                Err(error) => break Err(error),
                            }
                        };
                        let _ = listener.set_nonblocking(false);
                        accepted
                    })
                }),
            };
            match accepted {
                None => (9, 0),
                Some(Err(error)) if error.kind() == io::ErrorKind::WouldBlock => (11, 0),
                Some(Err(error)) => code(Err(error)),
                Some(Ok(stream)) => {
                    let mut table = system.files.lock().unwrap();
                    let handle = table.handle();
                    table.sockets.insert(handle, stream);
                    (0, handle)
                }
            }
        }
        "kush_sys_local_port" => {
            let fd = args.scalar(0);
            let table = system.files.lock().unwrap();
            if let Some(listener) = table.listeners.get(&fd) {
                code(
                    listener
                        .local_addr()
                        .map(|address| i64::from(address.port())),
                )
            } else if let Some(socket) = table.sockets.get(&fd) {
                code(socket.local_addr().map(|address| i64::from(address.port())))
            } else if let Some(address) = table.unbound.get(&fd) {
                (0, address.map_or(0, |address| i64::from(address.port())))
            } else {
                (9, 0)
            }
        }
        "kush_sys_stat" => {
            let field = args.scalar(1);
            match path(args, 0)? {
                Err(error) => code(Err(error)),
                Ok(path) => code(fs::metadata(path).and_then(|m| match field {
                    0 => Ok(i64::from(m.mode())),
                    1 => Ok(m.len().min(i64::MAX as u64) as i64),
                    _ => Err(io::Error::from_raw_os_error(22)),
                })),
            }
        }
        _ => {
            return Err(Diagnostic::new(
                span,
                format!("the reference interpreter has no shim for '{symbol}'"),
            ));
        }
    };
    Ok(host_result(status, HostValue::Scalar(value)))
}

/// The checked host operations. Their observable contract (buffer ownership,
/// errno values, bounded reads, explicit timeouts) mirrors the native
/// runtime's; the two implementations share no host call path.
pub(crate) fn host_call(
    system: &Host,
    op: HostOp,
    args: &mut dyn HostArgs,
    fuel: &mut usize,
    span: Span,
) -> Result<(i64, HostValue)> {
    *fuel = fuel
        .checked_sub(1)
        .ok_or_else(|| Diagnostic::new(span, "reference host computation budget exhausted"))?;
    let failure = |message: &str| Diagnostic::new(span, message.to_owned());
    match op {
        HostOp::FsRead => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.read path is not borrowed"))?;
            let (id, mut data, capacity) = args
                .take_buffer(1)
                .ok_or_else(|| failure("internal error: FS.read buffer is not owned"))?;
            if path.contains(&0) {
                args.consume_buffer(id);
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let mut file = match fs::File::open(path_from_bytes(&path)) {
                Ok(file) => file,
                Err(error) => {
                    args.consume_buffer(id);
                    return Ok(host_result(io_error_code(&error), HostValue::Scalar(0)));
                }
            };
            let initialized = data.len();
            data.resize(capacity, 0);
            let mut length = initialized;
            let mut probe = [0u8; 1];
            let status = loop {
                *fuel = fuel.checked_sub(1).ok_or_else(|| {
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
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
        HostOp::FsWrite | HostOp::FsAppend => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: host path is not borrowed"))?;
            let data = args
                .bytes(1)
                .ok_or_else(|| failure("internal error: host data is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
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
            Ok(host_result(status, HostValue::Scalar(data.len() as i64)))
        }
        HostOp::FsWriteExclusive => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: host path is not borrowed"))?;
            let data = args
                .bytes(1)
                .ok_or_else(|| failure("internal error: host data is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
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
            Ok(host_result(status, HostValue::Scalar(data.len() as i64)))
        }
        HostOp::FsRemove => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.remove path is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let status = fs::remove_file(path_from_bytes(&path))
                .err()
                .map_or(0, |error| io_error_code(&error));
            Ok(host_result(status, HostValue::Scalar(0)))
        }
        HostOp::FsRename => {
            let from = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.rename source is not borrowed"))?;
            let to = args
                .bytes(1)
                .ok_or_else(|| failure("internal error: FS.rename destination is not borrowed"))?;
            if from.contains(&0) || to.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let status = fs::rename(path_from_bytes(&from), path_from_bytes(&to))
                .err()
                .map_or(0, |error| io_error_code(&error));
            Ok(host_result(status, HostValue::Scalar(0)))
        }
        HostOp::FsMkdir => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.mkdir path is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let status = fs::create_dir(path_from_bytes(&path))
                .err()
                .map_or(0, |error| io_error_code(&error));
            Ok(host_result(status, HostValue::Scalar(0)))
        }
        HostOp::FsRemoveDir => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.remove_dir path is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let status = fs::remove_dir(path_from_bytes(&path))
                .err()
                .map_or(0, |error| io_error_code(&error));
            Ok(host_result(status, HostValue::Scalar(0)))
        }
        HostOp::FsList => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS.list path is not borrowed"))?;
            let (id, mut data, capacity) = args
                .take_buffer(1)
                .ok_or_else(|| failure("internal error: FS.list buffer is not owned"))?;
            if path.contains(&0) {
                args.consume_buffer(id);
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let mut status = 0;
            match fs::read_dir(path_from_bytes(&path)) {
                Ok(entries) => {
                    for entry in entries {
                        match entry {
                            Ok(entry) => {
                                let name = os_bytes(entry.file_name());
                                if let Some(failure) = append_bounded(&mut data, capacity, &name)
                                    .or_else(|| append_bounded(&mut data, capacity, b"\n"))
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
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
        HostOp::FsIsFile | HostOp::FsIsDir | HostOp::FsSize | HostOp::FsExists => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS metadata path is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
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
                    Ok(host_result(value.1, HostValue::Scalar(value.0)))
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
                    Ok(host_result(status, HostValue::Scalar(0)))
                }
                Err(error) => Ok(host_result(io_error_code(&error), HostValue::Scalar(0))),
            }
        }
        HostOp::FsOpen | HostOp::FsSyncDir => {
            let path = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: FS path is not borrowed"))?;
            if path.contains(&0) {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let path = path_from_bytes(&path);
            if op == HostOp::FsSyncDir {
                // Like the native `O_DIRECTORY` open: not a directory is ENOTDIR.
                let status = match fs::metadata(&path) {
                    Ok(metadata) if !metadata.is_dir() => 20,
                    _ => match fs::File::open(&path).and_then(|dir| dir.sync_all()) {
                        Ok(()) => 0,
                        Err(error) => io_error_code(&error),
                    },
                };
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            let mut options = OpenOptions::new();
            options.read(true);
            match args.scalar(1) {
                0 => {}
                1 => {
                    options.write(true).create(true);
                }
                2 => {
                    options.write(true);
                }
                3 => {
                    options.write(true).create_new(true);
                    #[cfg(unix)]
                    {
                        use std::os::unix::fs::OpenOptionsExt;
                        options.mode(0o600);
                    }
                }
                _ => return Ok(host_result(22, HostValue::Scalar(0))),
            }
            match options.open(path) {
                Ok(file) => {
                    let mut table = system.files.lock().unwrap();
                    table.next = table.next.max(2) + 1;
                    let handle = table.next;
                    table.open.insert(handle, file);
                    drop(table);
                    Ok(host_result(0, HostValue::Scalar(handle)))
                }
                Err(error) => Ok(host_result(io_error_code(&error), HostValue::Scalar(0))),
            }
        }
        HostOp::FsReadAt => {
            use std::os::unix::fs::FileExt;
            let (handle, offset, length) = (args.scalar(0), args.scalar(1), args.scalar(2));
            let (id, mut data, capacity) = args
                .take_buffer(3)
                .ok_or_else(|| failure("internal error: FS.read_at buffer is not owned"))?;
            let table = system.files.lock().unwrap();
            let status = match table.open.get(&handle) {
                None => 9, // EBADF
                Some(_) if offset < 0 || length < 0 => 22,
                Some(_) if length as u64 > (capacity - data.len()) as u64 => 27,
                Some(file) => {
                    let start = data.len();
                    data.resize(start + length as usize, 0);
                    let mut done = 0usize;
                    let status = loop {
                        if done == length as usize {
                            break 0;
                        }
                        match file.read_at(&mut data[start + done..], (offset as u64) + done as u64)
                        {
                            Ok(0) => break 0,
                            Ok(count) => done += count,
                            Err(error) if error.kind() == io::ErrorKind::Interrupted => {}
                            Err(error) => break io_error_code(&error),
                        }
                    };
                    data.truncate(start + done);
                    status
                }
            };
            drop(table);
            if status != 0 {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
        HostOp::FsWriteAt => {
            use std::os::unix::fs::FileExt;
            let (handle, offset) = (args.scalar(0), args.scalar(1));
            let data = args
                .bytes(2)
                .ok_or_else(|| failure("internal error: FS.write_at data is not borrowed"))?;
            let table = system.files.lock().unwrap();
            let status = match table.open.get(&handle) {
                None => 9,
                Some(_) if offset < 0 || data.len() as u64 > (i64::MAX - offset) as u64 => 22,
                Some(file) => match file.write_all_at(&data, offset as u64) {
                    Ok(()) => 0,
                    Err(error) => io_error_code(&error),
                },
            };
            drop(table);
            Ok(host_result(status, HostValue::Scalar(data.len() as i64)))
        }
        HostOp::FsSync | HostOp::FsTruncate | HostOp::FsFileSize | HostOp::FsClose => {
            let handle = args.scalar(0);
            let mut table = system.files.lock().unwrap();
            let (status, value) = match op {
                HostOp::FsClose => match table.open.remove(&handle) {
                    Some(_) => (0, 0),
                    None => (9, 0),
                },
                _ => match table.open.get(&handle) {
                    None => (9, 0),
                    Some(file) => {
                        let outcome = match op {
                            HostOp::FsSync => file.sync_all().map(|()| 0),
                            HostOp::FsTruncate if args.scalar(1) < 0 => {
                                Err(io::Error::from_raw_os_error(22))
                            }
                            HostOp::FsTruncate => file.set_len(args.scalar(1) as u64).map(|()| 0),
                            _ => file.metadata().map(|m| m.len().min(i64::MAX as u64) as i64),
                        };
                        match outcome {
                            Ok(value) => (0, value),
                            Err(error) => (io_error_code(&error), 0),
                        }
                    }
                },
            };
            drop(table);
            Ok(host_result(status, HostValue::Scalar(value)))
        }
        HostOp::EnvArgCount => {
            let count = system.args.len();
            Ok(host_result(0, HostValue::Scalar(count as i64)))
        }
        HostOp::EnvArg => {
            let index = args.scalar(0);
            let (id, mut data, capacity) = args
                .take_buffer(1)
                .ok_or_else(|| failure("internal error: ENV.arg buffer is not owned"))?;
            let Some(index) = usize::try_from(index)
                .ok()
                .filter(|index| *index < system.args.len())
            else {
                args.consume_buffer(id);
                return Ok(host_result(2, HostValue::Scalar(0)));
            };
            let value = system.args[index].clone();
            if let Some(status) = append_bounded(&mut data, capacity, &value) {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
        HostOp::EnvVarCount => {
            let count = system.environment.len();
            Ok(host_result(0, HostValue::Scalar(count as i64)))
        }
        HostOp::EnvVar => {
            let name = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: ENV.var name is not borrowed"))?;
            let (id, mut data, capacity) = args
                .take_buffer(1)
                .ok_or_else(|| failure("internal error: ENV.var buffer is not owned"))?;
            if name.contains(&0) {
                args.consume_buffer(id);
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let Some(value) = system.var(&name).map(<[u8]>::to_vec) else {
                args.consume_buffer(id);
                return Ok(host_result(2, HostValue::Scalar(0)));
            };
            if let Some(status) = append_bounded(&mut data, capacity, &value) {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
        HostOp::TimeUnixSeconds => {
            let seconds = match SystemTime::now().duration_since(UNIX_EPOCH) {
                Ok(duration) => i64::try_from(duration.as_secs()).unwrap_or(i64::MAX),
                Err(error) => -i64::try_from(error.duration().as_secs()).unwrap_or(i64::MAX),
            };
            Ok(host_result(0, HostValue::Scalar(seconds)))
        }
        HostOp::TimeMonotonicNs => Ok(host_result(0, HostValue::Scalar(system.monotonic_ns()))),
        HostOp::TimeSleepMs => {
            let milliseconds = args.scalar(0);
            if milliseconds < 0 {
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            thread::sleep(Duration::from_millis(milliseconds as u64));
            Ok(host_result(0, HostValue::Scalar(0)))
        }
        HostOp::ProcRun => {
            let program = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: PROC.run program is not borrowed"))?;
            let arguments = args
                .bytes(1)
                .ok_or_else(|| failure("internal error: PROC.run arguments are not borrowed"))?;
            let timeout = args.scalar(3);
            let Some((id, data, capacity)) = args.take_buffer(2) else {
                return Err(failure("internal error: PROC.run output is not a buffer"));
            };
            let initialized = data.len();
            let mut data = data;
            if timeout < 0 || program.is_empty() || program.contains(&0) {
                args.put_buffer(id, data);
                return Ok(host_result(22, HostValue::Scalar(0)));
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
                    args.put_buffer(id, data);
                    return Ok(host_result(io_error_code(&error), HostValue::Scalar(0)));
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
            let append_status = append_bounded(&mut data, capacity, &captured);
            args.put_buffer(id, data);
            // Overflow beats a concurrent deadline like the native loop,
            // which breaks the pipe loop before its timeout can re-arm.
            if overflow {
                return Ok(host_result(27, HostValue::Scalar(0)));
            }
            if let Some(error) = read_error {
                return Ok(host_result(error, HostValue::Scalar(0)));
            }
            if timed_out {
                return Ok(host_result(110, HostValue::Scalar(0)));
            }
            let Some(status) = status else {
                return Ok(host_result(5, HostValue::Scalar(0)));
            };
            if let Some(status_code) = append_status {
                return Ok(host_result(status_code, HostValue::Scalar(0)));
            }
            Ok(host_result(0, HostValue::Scalar(exit_status_code(status))))
        }
        HostOp::NetTcpExchange => {
            let host = args
                .bytes(0)
                .ok_or_else(|| failure("internal error: NET host is not borrowed"))?;
            let request = args
                .bytes(2)
                .ok_or_else(|| failure("internal error: NET request is not borrowed"))?;
            let port = args.scalar(1);
            let timeout_ms = args.scalar(4);
            let Some((id, data, capacity)) = args.take_buffer(3) else {
                return Err(failure("internal error: NET response is not a buffer"));
            };
            let mut data = data;
            let invalid = || host_result(22, HostValue::Scalar(0));
            if host.contains(&0) {
                args.put_buffer(id, data);
                return Ok(invalid());
            }
            let Ok(host) = String::from_utf8(host) else {
                args.put_buffer(id, data);
                return Ok(invalid());
            };
            let Ok(port) = u16::try_from(port) else {
                args.put_buffer(id, data);
                return Ok(invalid());
            };
            if port == 0 || timeout_ms < 0 {
                args.put_buffer(id, data);
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
                    args.put_buffer(id, data);
                    return Ok(host_result(io_error_code(&error), HostValue::Scalar(0)));
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
                args.put_buffer(id, data);
                return Ok(host_result(send_status, HostValue::Scalar(0)));
            }
            let _ = stream.shutdown(Shutdown::Write);
            let initialized = data.len();
            data.resize(capacity, 0);
            let mut length = initialized;
            let mut received_total = 0i64;
            let mut probe = [0u8; 1];
            let status = loop {
                *fuel = fuel.checked_sub(1).ok_or_else(|| {
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
            args.put_buffer(id, data);
            if status != 0 {
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            Ok(host_result(0, HostValue::Scalar(received_total)))
        }
        HostOp::OsStrerror => {
            let code = args.scalar(0);
            let (id, mut data, capacity) = args
                .take_buffer(1)
                .ok_or_else(|| failure("internal error: OS.strerror buffer is not owned"))?;
            if !(0..=4095).contains(&code) {
                args.consume_buffer(id);
                return Ok(host_result(22, HostValue::Scalar(0)));
            }
            let mut text = io::Error::from_raw_os_error(code as i32).to_string();
            if let Some(at) = text.rfind(" (os error ") {
                text.truncate(at);
            }
            if let Some(status) = append_bounded(&mut data, capacity, text.as_bytes()) {
                args.consume_buffer(id);
                return Ok(host_result(status, HostValue::Scalar(0)));
            }
            args.put_buffer(id, data);
            Ok(host_result(0, HostValue::Buffer(id)))
        }
    }
}
