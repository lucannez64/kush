//! Module-level constants, element access and method calls on places
//! (fields, references), two-phase exclusive borrows in calls, and wide
//! records. Every program runs on the reference evaluator and natively,
//! with balanced allocations; the rejections keep their soundness rules.

use kush::executable::check;

fn rejects(source: &str, fragment: &str) {
    let error = check(source).unwrap_err();
    assert!(
        error.message.contains(fragment),
        "expected {fragment:?}, got {error:?}"
    );
}

fn agrees(source: &str, expected_status: i64, expected_output: &str) {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}\n{source}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(stats.allocations, stats.deallocations, "{source}");
    assert_eq!(status, expected_status, "{source}");
    assert_eq!(
        String::from_utf8(output).unwrap(),
        expected_output,
        "{source}"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("places-and-constants-test");
        kush::native::build(&program, &binary).unwrap();
        let output = std::process::Command::new(&binary).output().unwrap();
        assert_eq!(
            output.status.code(),
            Some((expected_status as u64 & 255) as i32),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        assert_eq!(String::from_utf8(output.stdout).unwrap(), expected_output);
    }
}

#[test]
fn constants_are_their_values_at_each_use() {
    agrees(
        r#"
        const ZERO: u8 = 0x80;
        const BOTH: u8 = ZERO | 0x10;
        pub const WIDTH: i64 = 160;
        const AREA: i64 = WIDTH * 144;
        fn flag(on: Bool) -> u8 ! {} { if on { ZERO } else { 0 } }
        fn main() -> i64 ! {io, panic} {
            print_i64(Int.convert(flag(true)));
            print_i64(Int.convert(BOTH));
            print_i64(AREA);
            let low: u8 = BOTH & 0x0F;
            print_i64(Int.convert(low));
            0
        }
        "#,
        0,
        "128\n144\n23040\n0\n",
    );
    rejects(
        "const LOOP: i64 = LOOP + 1; fn main() -> i64 ! {panic} { LOOP }",
        "refers to itself",
    );
    rejects(
        "const BAD: u8 = 300; fn main() -> i64 ! {} { 0 } fn use_it() -> u8 ! {} { BAD }",
        "",
    );
}

#[test]
fn elements_of_fields_are_read_and_written_in_place() {
    agrees(
        r#"
        struct M { a: u8, memory: Vec<u8>, text: Bytes }
        fn read(m: &M, i: i64) -> u8 ! {panic} { m.memory[i] }
        fn read_byte(m: &M, i: i64) -> i64 ! {panic} { m.text[i] }
        fn write(m: &mut M, i: i64) -> Unit ! {panic} {
            // The value reads the owner whose field is written.
            m.memory[i] = m.a;
            m.a = m.memory[i - 1];
        }
        fn through(v: &mut Vec<u8>) -> Unit ! {panic} { v[0] = v[1]; }
        fn view(s: &mut [i64]) -> Unit ! {panic} { s[2] = s[0] + s[1]; s[0] = 5; }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut v: Vec<u8> = Vec.new();
            v = v.push(1);
            v = v.push(2);
            v = v.push(3);
            v[2] = 30;
            print_i64(Int.convert(v[2]));
            let mut m = M { a: 9, memory: v, text: Bytes.from("xy") };
            write(&mut m, 1);
            print_i64(Int.convert(read(&m, 1)));
            print_i64(Int.convert(m.a));
            print_i64(read_byte(&m, 1));
            print_i64(m.memory.len());
            through(&mut m.memory);
            print_i64(Int.convert(m.memory[0]));
            let mut array: [i64; 3] = [1, 2, 0];
            array[1] = 20;
            view(&mut array[..]);
            print_i64(array[0] + array[1] + array[2]);
            let mut k = 0;
            while k < 3 { array[k] = k * 100; k = k + 1; }
            print_i64(array[2]);
            0
        }
        "#,
        0,
        "30\n9\n1\n121\n3\n9\n46\n200\n",
    );
    rejects(
        r#"
        struct M { text: Bytes }
        fn write(m: &mut M) -> Unit ! {panic} { m.text[0] = 1; }
        fn main() -> i64 ! {} { 0 }
        "#,
        "Vec<u8>",
    );
    rejects(
        r#"
        struct M { memory: Vec<u8> }
        fn write(m: &M) -> Unit ! {panic} { m.memory[0] = 1; }
        fn main() -> i64 ! {} { 0 }
        "#,
        "shared",
    );
    rejects(
        r#"
        fn main() -> i64 ! {alloc, panic} {
            let mut boxes: Vec<Box<i64>> = Vec.new();
            boxes = boxes.push(Box.new(1));
            boxes[0] = Box.new(2);
            0
        }
        "#,
        "copyable element",
    );
}

#[test]
fn vector_fields_grow_in_place_through_method_syntax() {
    agrees(
        r#"
        struct Log { count: i64, items: Vec<u8> }
        fn record(log: &mut Log, value: u8) -> Unit ! {alloc, panic} {
            log.items.push(value);
            log.count = log.count + 1;
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut log = Log { count: 0, items: Vec.new() };
            record(&mut log, 4);
            record(&mut log, 2);
            print_i64(log.count);
            print_i64(log.items.len());
            print_i64(Int.convert(log.items[0]) * 10 + Int.convert(log.items[1]));
            0
        }
        "#,
        0,
        "2\n2\n42\n",
    );
}

#[test]
fn methods_are_called_on_fields_and_through_references() {
    agrees(
        r#"
        trait Counter {
            fn current(self: &Self) -> i64 ! {};
            fn bump(self: &mut Self) -> Unit ! {panic};
        }
        struct Plain { n: i64 }
        struct Owning { n: i64, history: Vec<i64> }
        impl Counter for Plain {
            fn current(self: &Self) -> i64 ! {} { self.n }
            fn bump(self: &mut Self) -> Unit ! {panic} { self.n = self.n + 1; }
        }
        impl Counter for Owning {
            fn current(self: &Self) -> i64 ! {} { self.n }
            fn bump(self: &mut Self) -> Unit ! {panic} { self.n = self.n + self.history.len(); }
        }
        struct Machine<C> { cycles: i64, counter: C }
        fn tick<C: Counter>(m: &mut Machine<C>) -> i64 ! {panic} {
            m.counter.bump();
            m.counter.bump();
            m.cycles = m.cycles + m.counter.current();
            m.cycles
        }
        fn twice<C: Counter>(c: &mut C) -> Unit ! {panic} { c.bump(); c.bump(); }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut plain = Machine { cycles: 0, counter: Plain { n: 0 } };
            print_i64(tick(&mut plain));
            twice(&mut plain.counter);
            print_i64(plain.counter.current());
            let mut history: Vec<i64> = Vec.new();
            history = history.push(7);
            history = history.push(8);
            let mut owning = Machine { cycles: 0, counter: Owning { n: 1, history: history } };
            print_i64(tick(&mut owning));
            0
        }
        "#,
        0,
        "2\n4\n5\n",
    );
    rejects(
        r#"
        struct P { x: i64 }
        impl P {
            fn bump(&mut self) -> Unit ! {panic} { self.x = self.x + 1; }
        }
        struct Q { p: P }
        fn call(q: &Q) -> Unit ! {panic} { q.p.bump(); }
        fn main() -> Unit ! {panic} {}
        "#,
        "shared",
    );
    rejects(
        r#"
        struct P { items: Vec<i64> }
        impl P { fn consume(self: Self) -> i64 ! {} { 0 } }
        struct Q { p: P }
        fn call(q: &mut Q) -> i64 ! {} { q.p.consume() }
        fn main() -> Unit ! {panic} {}
        "#,
        "cannot move an owned field",
    );
}

#[test]
fn an_exclusive_argument_is_taken_after_the_reads_of_its_owner() {
    agrees(
        r#"
        struct M { pc: u16, sp: u16, log: Vec<u8> }
        fn push(m: &mut M, value: u16) -> Unit ! {panic} { m.sp = value; }
        fn note(m: &mut M, a: i64, b: i64) -> Unit ! {io, panic} { print_i64(a * 10 + b); }
        fn shown(x: i64) -> i64 ! {io, panic} { print_i64(x); x }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut m = M { pc: 7, sp: 0, log: Vec.new() };
            push(&mut m, m.pc);
            print_i64(Int.convert(m.sp));
            let r = &mut m;
            push(r, r.pc + 1);
            print_i64(Int.convert(r.sp));
            // Arguments with effects keep their order.
            note(&mut m, shown(1), shown(2));
            m.log.push(Int.truncate(m.pc));
            print_i64(Int.convert(m.log[0]));
            0
        }
        "#,
        0,
        "7\n8\n1\n2\n12\n7\n",
    );
}

#[test]
fn records_have_no_size_or_field_limit() {
    // 300 fields, and a 1200-word record passed and returned by value.
    let fields: Vec<String> = (0..300).map(|i| format!("f{i}: i64")).collect();
    let values: Vec<String> = (0..300).map(|i| format!("f{i}: {i}")).collect();
    let part: Vec<String> = (0..300).map(|i| format!("p{i}: i64")).collect();
    let part_values: Vec<String> = (0..300).map(|i| format!("p{i}: seed + {i}")).collect();
    agrees(
        &format!(
            "struct Wide {{ {} }}
             struct Part {{ {} }}
             struct Huge {{ a: Part, b: Part, c: Part, d: Part }}
             fn make(seed: i64) -> Part ! {{panic}} {{ Part {{ {} }} }}
             fn bump(w: Wide) -> Wide ! {{panic}} {{
                 let mut v = w;
                 v.f0 = v.f0 + 1000;
                 v.f299 = v.f299 + 1;
                 v
             }}
             fn sum_parts(h: Huge) -> i64 ! {{panic}} {{ h.a.p0 + h.b.p150 + h.c.p299 + h.d.p1 }}
             fn grow(h: &mut Huge) -> Unit ! {{panic}} {{ h.d.p1 = h.d.p1 * 2; }}
             fn main() -> i64 ! {{io, panic}} {{
                 let v = bump(Wide {{ {} }});
                 print_i64(v.f0);
                 print_i64(v.f150);
                 print_i64(v.f299);
                 let mut h = Huge {{ a: make(0), b: make(1), c: make(2), d: make(3) }};
                 grow(&mut h);
                 sum_parts(h)
             }}",
            fields.join(", "),
            part.join(", "),
            part_values.join(", "),
            values.join(", ")
        ),
        460,
        "1000\n150\n300\n",
    );
    // Other inline layouts keep their 32-word limit.
    let fields = vec!["i64"; 32].join(",");
    rejects(
        &format!("enum Wide {{ Value({fields}) }} fn main() -> Unit ! {{}} {{}}"),
        "32-word",
    );
}

#[test]
fn fields_of_mutable_record_locals_are_assigned_in_place() {
    agrees(
        r#"
        struct Inner { v: i64 }
        struct Cpu { a: i64, halted: Bool, inner: Inner }
        fn main() -> i64 ! {io, panic} {
            let mut cpu = Cpu { a: 1, halted: true, inner: Inner { v: 2 } };
            cpu.a = cpu.a + 40;
            cpu.halted = false;
            cpu.inner.v = cpu.inner.v * 10;
            print_i64(cpu.a);
            print_i64(cpu.inner.v);
            if cpu.halted { 1 } else { 0 }
        }
        "#,
        0,
        "41\n20\n",
    );
    rejects(
        r#"
        struct Cpu { a: i64 }
        fn main() -> i64 ! {panic} { let cpu = Cpu { a: 1 }; cpu.a = 2; cpu.a }
        "#,
        "let mut",
    );
    rejects(
        r#"
        struct Holder { items: Vec<i64> }
        fn main() -> i64 ! {alloc, panic} {
            let mut h = Holder { items: Vec.new() };
            h.items = Vec.new();
            0
        }
        "#,
        "copyable",
    );
}

#[test]
fn a_field_write_is_seen_by_later_overflow_checks() {
    // The prover may know `p.x == 1` from the literal; after the field write
    // that fact is gone, so the addition stays checked and panics.
    let program = check(
        r#"
        struct P { x: i64 }
        fn main() -> i64 ! {panic} {
            let mut p = P { x: 1 };
            p.x = 9223372036854775807;
            p.x + 1
        }
        "#,
    )
    .unwrap();
    let mut output = Vec::new();
    assert!(program.evaluate_with_stats(&mut output).is_err());
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("field-write-overflow");
        kush::native::build(&program, &binary).unwrap();
        let status = std::process::Command::new(&binary).status().unwrap();
        assert!(!status.success());
    }
}

#[test]
fn fields_inside_owning_fields_are_reached_through_references() {
    // `o.inner` owns a vector; its scalar fields are still plain places.
    agrees(
        r#"
        struct Inner { on: Bool, n: i64, log: Vec<i64> }
        struct Outer { a: i64, inner: Inner }
        fn peek(o: &Outer) -> i64 ! {panic} { if o.inner.on { o.inner.n } else { 0 } }
        fn poke(o: &mut Outer) -> Unit ! {alloc, panic} {
            o.inner.n = o.inner.n + 1;
            o.inner.log.push(o.inner.n);
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut o = Outer { a: 1, inner: Inner { on: true, n: 41, log: Vec.new() } };
            poke(&mut o);
            print_i64(o.inner.log.len());
            peek(&o)
        }
        "#,
        42,
        "1\n",
    );
    rejects(
        r#"
        struct Inner { log: Vec<i64> }
        struct Outer { inner: Inner }
        fn steal(o: &Outer) -> Vec<i64> ! {} { o.inner.log }
        fn main() -> i64 ! {} { 0 }
        "#,
        "cannot move owned field",
    );
}

#[test]
fn disjoint_owning_fields_are_borrowed_together() {
    agrees(
        r#"
        struct Inner { n: i64, v: Vec<i64> }
        struct O { x: Inner, y: Vec<i64> }
        fn both(a: &mut Inner, b: &mut Vec<i64>) -> Unit ! {alloc, panic} {
            a.n = a.n + 1;
            b.push(a.n);
            a.v.push(7);
        }
        fn via(o: &mut O) -> Unit ! {alloc, panic} {
            both(&mut o.x, &mut o.y);
            both(&mut o.x, &mut o.y);
        }
        fn main() -> i64 ! {io, alloc, panic} {
            let mut o = O { x: Inner { n: 40, v: Vec.new() }, y: Vec.new() };
            via(&mut o);
            both(&mut o.x, &mut o.y);
            print_i64(o.y.len() * 100 + o.x.v.len());
            o.x.n
        }
        "#,
        43,
        "303\n",
    );
    // The same field twice still aliases, from a local or a reference.
    rejects(
        r#"
        struct O { y: Vec<i64> }
        fn same(a: &mut Vec<i64>, b: &mut Vec<i64>) -> Unit ! {} {}
        fn main() -> i64 ! {alloc, panic} { let mut o = O { y: Vec.new() }; same(&mut o.y, &mut o.y); 0 }
        "#,
        "overlapping",
    );
    rejects(
        r#"
        struct O { y: Vec<i64>, z: Vec<i64> }
        fn same(a: &mut Vec<i64>, b: &mut Vec<i64>) -> Unit ! {} {}
        fn via(o: &mut O) -> Unit ! {} { same(&mut o.y, &mut o.y); }
        fn main() -> i64 ! {} { 0 }
        "#,
        "overlapping",
    );
}
