use kush::executable::{MemoryStats, check};
use std::io::{self, Read, Write};

const RESULT: &str = "enum Result<T,E>{Ok(T),Err(E)}";

#[test]
fn line_reads_stop_at_newline_preserve_following_input_and_bound_storage() {
    for (capacity, input, status, output, remaining) in [
        (
            4,
            b"ab\ncd".as_slice(),
            0,
            b"ab\n".as_slice(),
            b"cd".as_slice(),
        ),
        (3, b"ab\ncd", 0, b"ab\n", b"cd"),
        (4, b"abc", 0, b"abc", b""),
        (0, b"", 0, b"", b""),
        (0, b"\nx", 27, b"", b"x"),
        (2, b"ab\ncd", 27, b"", b"cd"),
    ] {
        let source = read_program(capacity).replace("IO.read_all", "IO.read_line");
        let mut input = input;
        let mut out = Vec::new();
        let (actual, stats) = check(&source)
            .unwrap()
            .evaluate_with_io_and_stats(&mut input, &mut out)
            .unwrap();
        assert_eq!(actual, status);
        assert_eq!(out, output);
        assert_eq!(input, remaining);
        assert_eq!(stats.allocations, stats.deallocations);
        assert_eq!(stats.buffer_growths, 0);
    }
}

#[test]
fn todo_session_changes_state_filters_and_handles_invalid_commands() {
    let source = include_str!("../../../examples/todo.kush");
    let (status, output, _) = evaluate(
        source,
        b"a Buy milk\na Write Kush\nt 1\nf done\nf open\nd 2\nt 99\na \x1b[2J\nq\n",
    );
    assert_eq!(status, 0);
    let output = String::from_utf8(output).unwrap();
    for expected in [
        "1  [ ] Buy milk",
        "1  [x] Buy milk",
        "2  [ ] Write Kush",
        "view: done",
        "view: open",
        "Task deleted.",
        "Use a task ID between 1 and 32.",
        "Titles must use printable ASCII",
        "Goodbye.",
    ] {
        assert!(output.contains(expected), "missing {expected}: {output}");
    }
    assert!(!output.contains("[ ] \x1b"));
    assert_eq!(evaluate(source, b"").0, 0);
}
fn evaluate(source: &str, input: &[u8]) -> (i64, Vec<u8>, MemoryStats) {
    let mut output = Vec::new();
    let (status, stats) = check(source)
        .unwrap()
        .evaluate_with_io_and_stats(&mut &input[..], &mut output)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    (status, output, stats)
}
fn read_program(capacity: i64) -> String {
    format!(
        r#"{RESULT}
        #[noalloc] #[nosuspend]
        fn copy(input:Stdin,output:Stdout,buffer:Bytes)->Result<Unit,i64> ! {{io}} {{
            let bytes=IO.read_all(input,buffer)?;
            IO.write(output,&bytes)
        }}
        fn main()->i64 ! {{io,alloc,panic}} {{
            match copy(IO.stdin(),IO.stdout(),Bytes.with_capacity({capacity})) {{Ok(_)=>0,Err(code)=>code}}
        }}"#
    )
}

#[test]
fn bounded_io_is_byte_preserving_and_does_not_grow_buffers() {
    for input in [b"".as_slice(), b"a", b"\0\xff\xc3\xa9"] {
        let (status, output, stats) = evaluate(&read_program(4), input);
        assert_eq!(status, 0);
        assert_eq!(output, input);
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.buffer_growths, 0);
    }
    assert_eq!(evaluate(&read_program(0), b"").0, 0);
    let (status, output, stats) = evaluate(&read_program(0), b"x");
    assert_eq!(status, 27);
    assert!(output.is_empty());
    assert_eq!(stats.deallocations, 1);
}

#[test]
fn capacity_errors_reclaim_input_and_consume_only_one_excess_probe_byte() {
    let program = check(&read_program(1)).unwrap();
    let mut input = b"abc".as_slice();
    let (status, stats) = program
        .evaluate_with_io_and_stats(&mut input, &mut Vec::new())
        .unwrap();
    assert_eq!(status, 27);
    assert_eq!(input, b"c");
    assert_eq!(stats.allocations, stats.deallocations);
}

#[test]
fn reading_appends_to_initialized_bytes_and_accepts_exact_capacity() {
    let source = format!(
        r#"{RESULT}
        fn main()->i64 ! {{io,alloc,panic}} {{
            let input=IO.stdin();let output=IO.stdout();
            let b=Bytes.push_reserved(Bytes.with_capacity(3),65);
            match IO.read_all(input,b) {{
                Ok(bytes)=>match IO.write(output,&bytes) {{Ok(_)=>0,Err(code)=>code}},
                Err(code)=>code,
            }}
        }}"#
    );
    let (status, output, stats) = evaluate(&source, b"BC");
    assert_eq!(status, 0);
    assert_eq!(output, b"ABC");
    assert_eq!(stats.buffer_growths, 0);
}

struct InterruptedShortRead<'a> {
    bytes: &'a [u8],
    interrupt: bool,
    failure: Option<i32>,
}
impl Read for InterruptedShortRead<'_> {
    fn read(&mut self, destination: &mut [u8]) -> io::Result<usize> {
        if self.interrupt {
            self.interrupt = false;
            return Err(io::ErrorKind::Interrupted.into());
        }
        if self.bytes.is_empty() {
            return self
                .failure
                .map_or(Ok(0), |code| Err(io::Error::from_raw_os_error(code)));
        }
        let count = destination.len().min(self.bytes.len()).min(2);
        destination[..count].copy_from_slice(&self.bytes[..count]);
        self.bytes = &self.bytes[count..];
        Ok(count)
    }
}
struct ShortWrite {
    bytes: Vec<u8>,
    interrupt: bool,
    fail_after: Option<usize>,
    zero: bool,
}
impl Write for ShortWrite {
    fn write(&mut self, source: &[u8]) -> io::Result<usize> {
        if self.interrupt {
            self.interrupt = false;
            return Err(io::ErrorKind::Interrupted.into());
        }
        if self
            .fail_after
            .is_some_and(|limit| self.bytes.len() >= limit)
        {
            return Err(io::Error::from_raw_os_error(32));
        }
        if self.zero {
            return Ok(0);
        }
        let count = source.len().min(2);
        self.bytes.extend_from_slice(&source[..count]);
        Ok(count)
    }
    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}
#[test]
fn interrupted_and_short_transfers_retry_without_losing_bytes() {
    let mut input = InterruptedShortRead {
        bytes: b"abcdef",
        interrupt: true,
        failure: None,
    };
    let mut output = ShortWrite {
        bytes: Vec::new(),
        interrupt: true,
        fail_after: None,
        zero: false,
    };
    let (status, stats) = check(&read_program(6))
        .unwrap()
        .evaluate_with_io_and_stats(&mut input, &mut output)
        .unwrap();
    assert_eq!(status, 0);
    assert_eq!(output.bytes, b"abcdef");
    assert_eq!(stats.allocations, stats.deallocations);
}

#[test]
fn partial_io_failures_are_recoverable_and_all_owners_are_reclaimed() {
    let program = check(&read_program(6)).unwrap();
    let mut input = InterruptedShortRead {
        bytes: b"ab",
        interrupt: true,
        failure: Some(9),
    };
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_io_and_stats(&mut input, &mut output)
        .unwrap();
    assert_eq!(status, 9);
    assert!(output.is_empty());
    assert_eq!(stats.allocations, stats.deallocations);
    for zero in [false, true] {
        let mut output = ShortWrite {
            bytes: Vec::new(),
            interrupt: true,
            fail_after: Some(2),
            zero,
        };
        let (status, stats) = program
            .evaluate_with_io_and_stats(&mut b"abcdef".as_slice(), &mut output)
            .unwrap();
        assert_eq!(status, if zero { 5 } else { 32 });
        assert_eq!(
            output.bytes,
            if zero {
                b"".as_slice()
            } else {
                b"ab".as_slice()
            }
        );
        assert_eq!(stats.allocations, stats.deallocations);
    }
}

#[test]
fn repeated_io_interrupts_exhaust_the_reference_budget() {
    struct NeverReady;
    impl Read for NeverReady {
        fn read(&mut self, _: &mut [u8]) -> io::Result<usize> {
            Err(io::ErrorKind::Interrupted.into())
        }
    }
    let error = check(&read_program(1))
        .unwrap()
        .evaluate_with_io(&mut NeverReady, &mut Vec::new())
        .unwrap_err();
    assert!(error.message.contains("I/O computation budget"));
}

#[test]
fn conventional_result_tags_and_error_payloads_are_not_hardcoded() {
    let source = read_program(2).replace(RESULT, "enum Result<T,E>{Err(E),Ok(T)}");
    assert_eq!(evaluate(&source, b"hi").1, b"hi");
    assert_eq!(evaluate(&source, b"abc").0, 27);
}

#[test]
fn capabilities_types_effects_and_affine_transfers_are_checked() {
    for body in [
        "IO.read_all(IO.stdout(),Bytes.with_capacity(1));",
        "IO.read_all(IO.stdin(),1);",
        "IO.write(IO.stdin(),&b);",
        "IO.write(IO.stdout(),b);",
        "IO.write(1,&b);",
        "IO.read_all(IO.stdin(),b);drop(b);",
        "IO.write(IO.stdout(),&b);drop(b);drop(b);",
        "IO.stdin()==IO.stdin();",
        "IO.read_all();",
        "IO.write();",
    ] {
        let source = format!(
            r#"{RESULT} fn main()->Unit ! {{io,alloc,panic}} {{let b=Bytes.with_capacity(1);{body}}}"#
        );
        assert!(check(&source).is_err(), "{body}");
    }
    for source in [
        "fn f()->Stdin ! {} {IO.stdin()}",
        "fn f()->Stdout ! {} {IO.stdout()}",
        "fn f(s:Stdin,b:Bytes)->Result<Bytes,i64> ! {} {IO.read_all(s,b)}",
        "fn f(s:Stdout,b:&Bytes)->Result<Unit,i64> ! {} {IO.write(s,b)}",
    ] {
        let error = check(&format!("{RESULT} {source}")).unwrap_err();
        assert!(error.message.contains("requires effects {io}"), "{error:?}");
    }
    for prefix in [
        "",
        "enum Result<T,E>{Ok(E),Err(T)}",
        "enum Result<T,E>{Ok(T),Err(E),Other}",
    ] {
        let source = format!(
            "{prefix} fn main()->Unit ! {{io,alloc,panic}} {{IO.read_all(IO.stdin(),Bytes.with_capacity(1));}}"
        );
        let error = check(&source).unwrap_err();
        assert!(error.message.contains("I/O requires"), "{error:?}");
    }
}

#[test]
fn stream_values_can_be_passed_stored_and_matched_without_owning_descriptors() {
    let source = format!(
        r#"{RESULT} enum Streams{{Pair(Stdin,Stdout)}}
        fn main()->i64 ! {{io,alloc,panic}} {{
            let streams=Streams.Pair(IO.stdin(),IO.stdout());
            match streams {{Streams.Pair(input,output)=>{{
                let bytes=IO.read_all(input,Bytes.with_capacity(2));
                match bytes {{Ok(b)=>match IO.write(output,&b){{Ok(_)=>0,Err(e)=>e}},Err(e)=>e}}
            }}}}
        }}"#
    );
    assert_eq!(evaluate(&source, b"ok").1, b"ok");
}

#[test]
fn stdin_parser_and_stdio_examples_work_with_injected_input() {
    let example = include_str!("../../../examples/expression-stdin.kush");
    for (input, expected) in [
        ("12 + 3 * 10\n", "42\n"),
        ("2*3+4", "10\n"),
        ("1+2*3+", "6\n"),
        ("9223372036854775808", "-1\n"),
    ] {
        let (status, output, _) = evaluate(example, input.as_bytes());
        assert_eq!(status, 0);
        assert_eq!(output, expected.as_bytes());
    }
    let (status, output, _) = evaluate(example, &vec![b'1'; 4097]);
    assert_eq!(status, 1);
    assert_eq!(output, b"-27\n");
    assert_eq!(
        evaluate(include_str!("../../../examples/stdio.kush"), b"a\0\xff").1,
        b"a\0\xff"
    );
}

#[test]
fn streaming_copy_reuses_one_allocation_across_short_reads_and_eof() {
    let source = include_str!("../../../examples/stream-copy.kush");
    for input in [b"".as_slice(), b"abc", &vec![b'z'; 20000]] {
        let (status, out, stats) = evaluate(source, input);
        assert_eq!(status, 0);
        assert_eq!(out, input);
        assert_eq!(stats.allocations, 1);
        assert_eq!(stats.buffer_growths, 0);
    }
    let mut input = InterruptedShortRead {
        bytes: b"short reads",
        interrupt: true,
        failure: None,
    };
    let mut out = Vec::new();
    let (status, stats) = check(source)
        .unwrap()
        .evaluate_with_io_and_stats(&mut input, &mut out)
        .unwrap();
    assert_eq!(status, 0);
    assert_eq!(out, b"short reads");
    assert_eq!(stats.allocations, 1);
    assert_eq!(stats.deallocations, 1);
    let mut input = InterruptedShortRead {
        bytes: b"partial",
        interrupt: false,
        failure: Some(9),
    };
    let (status, stats) = check(source)
        .unwrap()
        .evaluate_with_io_and_stats(&mut input, &mut Vec::new())
        .unwrap();
    assert_eq!(status, 1);
    assert_eq!(stats.allocations, stats.deallocations);
}

#[test]
fn chunk_reads_append_without_probing_and_full_buffers_consume_no_input() {
    for (capacity, prefix, expected, left, status) in [
        (3, false, b"abc".as_slice(), b"def".as_slice(), 0),
        (3, true, b"Xab", b"cdef", 0),
        (0, false, b"", b"abcdef", 27),
        (1, true, b"", b"abcdef", 27),
    ] {
        let constructor = if prefix {
            format!("Bytes.push_reserved(Bytes.with_capacity({capacity}), 88)")
        } else {
            format!("Bytes.with_capacity({capacity})")
        };
        let source = read_program(capacity)
            .replace("IO.read_all", "IO.read_chunk")
            .replace(&format!("Bytes.with_capacity({capacity})"), &constructor);
        let mut input = b"abcdef".as_slice();
        let mut out = Vec::new();
        let (actual, stats) = check(&source)
            .unwrap()
            .evaluate_with_io_and_stats(&mut input, &mut out)
            .unwrap();
        assert_eq!(actual, status);
        assert_eq!(out, expected);
        assert_eq!(input, left);
        assert_eq!(stats.allocations, stats.deallocations);
    }
}

#[test]
fn clear_keeps_capacity_and_cannot_invalidate_live_views_or_erase_linear_obligations() {
    let source = r#"#[noalloc] #[nosuspend]
        fn reset(b: Bytes) -> Bytes ! {} { Bytes.clear(b) }
        fn main() -> i64 ! {alloc, panic} {
            let b = reset(Bytes.from("abc"));
            let n = Bytes.capacity(&b) + Bytes.len(&b);
            let b = Bytes.push_reserved(b, 90);
            n + Bytes.get(&b, 0)
        }"#;
    assert_eq!(evaluate(source, b"").0, 93);
    for source in [
        "fn main()->i64 ! {alloc,panic} { let b=Bytes.from(\"abc\");let v=&b[..];let b=Bytes.clear(b);Slice.get(v,0) }",
        "fn main()->Unit ! {alloc,panic} { let b: Bytes @[1]=Bytes.from(\"abc\");drop(Bytes.clear(b)); }",
    ] {
        assert!(check(source).is_err());
    }
}
