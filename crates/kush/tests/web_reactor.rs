//! WEB-REACTOR: a task waiting for a socket or a timer suspends instead of
//! blocking the thread. Natively the scheduler sleeps in epoll_wait when no
//! task is ready; the reference evaluator polls waiting tasks in a fixed
//! order. Every program prints only in a deterministic order (after joins),
//! and both backends must agree.
#![cfg(all(target_os = "linux", target_arch = "x86_64"))]

use kush::Host;
use kush::executable;
use std::io;
use std::process::{Command, Stdio};

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<web-reactor-test>", source).unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str) -> String {
    let program = checked(source);
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_host_and_stats(&mut io::empty(), &mut output, &Host::empty())
        .unwrap();
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    assert_eq!(stats.allocations, stats.deallocations, "reference cleanup must be balanced");
    String::from_utf8(output).unwrap()
}

fn native(source: &str) -> String {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("reactor");
    kush::native::build(&program, &binary).unwrap();
    let output = Command::new(&binary).stdin(Stdio::null()).output().unwrap();
    assert_eq!(
        output.status.code(),
        Some(0),
        "{}{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    String::from_utf8(output.stdout).unwrap()
}

fn both(source: &str, expected: &str) {
    let reference = reference(source);
    assert_eq!(reference, expected, "reference");
    assert_eq!(native(source), expected, "native");
}

const PRELUDE: &str = r#"
use std.net;
use std.net.Conn;
use std.net.Listener;
use std.result.Result;
use std.task.TaskExit;
use std.time;

fn now() -> i64 ! {io} {
    match time.monotonic_ns() { Result.Ok(ns) => ns, Result.Err(_) => 0 }
}

fn show(exit: TaskExit<i64>) -> Unit ! {io, panic} {
    match exit {
        TaskExit.Completed(value) => print_i64(value),
        TaskExit.Cancelled => print_i64(-1),
    }
}
"#;

const SERVER_AND_CLIENTS: &str = r#"
/// Read until the peer closes; the bytes read, or minus the errno.
fn read_all(conn: &Conn) -> Result<Bytes, i64> ! {io, alloc, panic, suspend} {
    let mut buffer = Bytes.with_capacity(64);
    loop {
        let before = Bytes.len(&buffer);
        buffer = match net.read(conn, buffer, 5000) {
            Result.Ok(next) => next,
            Result.Err(code) => { return Result.Err(code); },
        };
        if Bytes.len(&buffer) == before { return Result.Ok(buffer); }
    }
}

/// Echo one request back with a '!' after it.
fn handle(conn: Conn) -> Unit ! {io, alloc, panic, suspend} {
    match read_all(&conn) {
        Result.Ok(request) => {
            let reply = Bytes.push(request, 33);
            let _ = net.write(&conn, &reply, 5000);
        },
        Result.Err(code) => print_i64(-code),
    }
    let _ = net.close(conn);
}

/// Accept `count` connections, each served by its own task.
fn serve(listener: Listener, count: i64) -> i64 ! {io, alloc, panic, suspend} {
    Task.scope(fn() -> i64 ! {io, alloc, panic, suspend} {
        let mut served = 0;
        while served < count {
            match net.accept(&listener, 5000) {
                Result.Ok(conn) => {
                    Task.spawn(fn() -> Unit ! {io, alloc, panic, suspend} { handle(conn) });
                },
                Result.Err(code) => { print_i64(-code); },
            }
            served = served + 1;
        }
        let _ = net.close_listener(listener);
        served
    })
}

/// Send `size` bytes, close the sending side, and return the reply's length
/// times 1000 plus its last byte.
fn client(port: i64, size: i64) -> i64 ! {io, alloc, panic, suspend} {
    let host = Bytes.from("127.0.0.1");
    let conn = match net.connect(&host, port, 5000) {
        Result.Ok(conn) => conn,
        Result.Err(code) => { return -code; },
    };
    let mut request = Bytes.with_capacity(size);
    let mut i = 0;
    while i < size {
        request = Bytes.push(request, 97);
        i = i + 1;
    }
    let _ = net.write(&conn, &request, 5000);
    let _ = net.shutdown(&conn, 1);
    let result = match read_all(&conn) {
        Result.Ok(reply) => {
            let length = Bytes.len(&reply);
            if length > 0 { length * 1000 + Bytes.get(&reply, length - 1) } else { 0 }
        },
        Result.Err(code) => -code,
    };
    let _ = net.close(conn);
    result
}

fn main() -> i64 ! {io, alloc, panic, suspend} {
    let host = Bytes.from("127.0.0.1");
    let listener = match net.listen(&host, 0, 16, false) {
        Result.Ok(listener) => listener,
        Result.Err(code) => { return code; },
    };
    let port = match net.local_port(&listener) { Result.Ok(port) => port, Result.Err(_) => 0 };
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { serve(listener, 4) });
        let a = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { client(port, 1) });
        let b = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { client(port, 2) });
        let c = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { client(port, 30) });
        let d = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { client(port, 4) });
        show(Task.join(a));
        show(Task.join(b));
        show(Task.join(c));
        show(Task.join(d));
        show(Task.join(server));
    });
    0
}
"#;

/// One thread serves four connections while four client tasks talk to it:
/// with blocking sockets the first client's read would stall everything.
#[test]
fn a_server_and_its_clients_share_one_thread() {
    both(
        &format!("{PRELUDE}{SERVER_AND_CLIENTS}"),
        "2033\n3033\n31033\n5033\n4\n",
    );
}

const TIMERS: &str = r#"
fn sleeper(milliseconds: i64, mark: i64) -> i64 ! {io, panic, suspend} {
    match time.wait_ms(milliseconds) {
        Result.Ok(_) => mark,
        Result.Err(code) => -code,
    }
}

fn main() -> i64 ! {io, alloc, panic, suspend} {
    let start = now();
    // Each task records when it woke; the joins print in a fixed order.
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let slow = Task.spawn(fn() -> i64 ! {io, panic, suspend} { sleeper(200, 3) });
        let fast = Task.spawn(fn() -> i64 ! {io, panic, suspend} { let r = sleeper(100, 1); if now() - start < 190000000 { r } else { -9 } });
        let middle = Task.spawn(fn() -> i64 ! {io, panic, suspend} { sleeper(150, 2) });
        show(Task.join(fast));
        show(Task.join(middle));
        show(Task.join(slow));
    });
    // Concurrent: about 200 ms, not the 450 ms of three sleeps in a row.
    let elapsed = now() - start;
    print_i64(if elapsed >= 200000000 && elapsed < 400000000 { 1 } else { elapsed });
    // Outside a task scope, main is the only task and simply sleeps.
    print_i64(sleeper(5, 7));
    print_i64(match time.wait_ms(-1) { Result.Ok(_) => 0, Result.Err(code) => code });
    0
}
"#;

#[test]
fn timers_wake_tasks_concurrently_in_deadline_order() {
    both(&format!("{PRELUDE}{TIMERS}"), "1\n2\n3\n1\n7\n22\n");
}

const CANCEL: &str = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let host = Bytes.from("127.0.0.1");
    let listener = match net.listen(&host, 0, 16, false) {
        Result.Ok(listener) => listener,
        Result.Err(code) => { return code; },
    };
    let start = now();
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        // Both wait with no timeout; cancelling them wakes them.
        let sleeping = Task.spawn(fn() -> i64 ! {io, panic, suspend} {
            match time.wait_ms(60000) { Result.Ok(_) => 0, Result.Err(code) => { print_i64(code); code } }
        });
        let accepting = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            let code = match net.accept(&listener, 0) {
                Result.Ok(conn) => { let _ = net.close(conn); 0 },
                Result.Err(code) => code,
            };
            let _ = net.close_listener(listener);
            print_i64(code);
            code
        });
        let _ = Task.yield();
        Task.cancel(&sleeping);
        Task.cancel(&accepting);
        show(Task.join(sleeping));
        show(Task.join(accepting));
    });
    print_i64(if now() - start < 5000000000 { 1 } else { 0 });
    0
}
"#;

#[test]
fn cancelling_a_waiting_task_wakes_it() {
    both(&format!("{PRELUDE}{CANCEL}"), "125\n125\n-1\n-1\n1\n");
}

const STARVATION: &str = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let start = now();
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        // A task that only yields for 300 ms must not keep a 5 ms timer
        // from firing.
        let busy = Task.spawn(fn() -> i64 ! {io, panic, suspend} {
            while now() - start < 300000000 { let _ = Task.yield(); }
            2
        });
        let timer = Task.spawn(fn() -> i64 ! {io, panic, suspend} {
            let _ = time.wait_ms(5);
            if now() - start < 250000000 { 1 } else { -1 }
        });
        show(Task.join(timer));
        show(Task.join(busy));
    });
    0
}
"#;

#[test]
fn a_yielding_task_does_not_starve_a_waiting_one() {
    both(&format!("{PRELUDE}{STARVATION}"), "1\n2\n");
}

/// Many connections at once: 200 client tasks, each served by its own
/// handler task, all on one thread (natively; the evaluator's polling model
/// is a test oracle, not meant for load).
#[test]
fn two_hundred_connections_on_one_thread() {
    let main = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let host = Bytes.from("127.0.0.1");
    let listener = match net.listen(&host, 0, 512, false) {
        Result.Ok(listener) => listener,
        Result.Err(code) => { return code; },
    };
    let port = match net.local_port(&listener) { Result.Ok(port) => port, Result.Err(_) => 0 };
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        let server = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} { serve(listener, 200) });
        let mut i = 0;
        while i < 200 {
            Task.spawn(fn() -> Unit ! {io, alloc, panic, suspend} {
                let result = client(port, 3);
                if result != 4033 { print_i64(result); }
            });
            i = i + 1;
        }
        show(Task.join(server));
    });
    0
}
"#;
    let source = format!("{PRELUDE}{}", SERVER_AND_CLIENTS.split("fn main()").next().unwrap()) + main;
    assert_eq!(native(&source), "200\n");
}

const PROPAGATE: &str = r#"
fn main() -> i64 ! {io, alloc, panic, suspend} {
    let start = now();
    Task.scope(fn() -> Unit ! {io, alloc, panic, suspend} {
        // A grandchild waiting a minute wakes when its grandparent is
        // cancelled (TASK-CANCEL-PROPAGATE).
        let parent = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
            Task.scope(fn() -> i64 ! {io, alloc, panic, suspend} {
                let child = Task.spawn(fn() -> i64 ! {io, alloc, panic, suspend} {
                    Task.scope(fn() -> i64 ! {io, alloc, panic, suspend} {
                        let grandchild = Task.spawn(fn() -> i64 ! {io, panic, suspend} {
                            match time.wait_ms(60000) { Result.Ok(_) => 0, Result.Err(code) => code }
                        });
                        match Task.join(grandchild) { TaskExit.Completed(v) => v, TaskExit.Cancelled => -1 }
                    })
                });
                match Task.join(child) { TaskExit.Completed(v) => v, TaskExit.Cancelled => -1 }
            })
        });
        let _ = time.wait_ms(20);
        Task.cancel(&parent);
        show(Task.join(parent));
    });
    print_i64(if now() - start < 5000000000 { 1 } else { 0 });
    0
}
"#;

#[test]
fn cancelling_a_task_cancels_its_descendants() {
    both(&format!("{PRELUDE}{PROPAGATE}"), "-1\n1\n");
}
