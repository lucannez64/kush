//! SIMD-X86-SHA: the x86 SHA intrinsics of `std.x86`. The reference
//! evaluator runs their Kush specification (written from Intel's
//! definitions); native builds run the real instructions. On random inputs
//! both must agree, which checks the specification against the CPU.
use kush::executable::check;

struct Rng(u64);
impl Rng {
    fn next(&mut self) -> u32 {
        self.0 = self
            .0
            .wrapping_mul(6364136223846793005)
            .wrapping_add(1442695040888963407);
        (self.0 >> 32) as u32
    }
    fn vector(&mut self) -> String {
        format!(
            "u32x4.new({}, {}, {}, {})",
            self.next(),
            self.next(),
            self.next(),
            self.next()
        )
    }
}

fn program() -> String {
    let mut rng = Rng(2026);
    let mut body = String::new();
    for _ in 0..24 {
        let (a, b, c) = (rng.vector(), rng.vector(), rng.vector());
        body.push_str(&format!(
            "let a = {a}; let b = {b}; let c = {c};
             show(x86.sha256rnds2(&sha, a, b, c));
             show(x86.sha256msg1(&sha, a, b));
             show(x86.sha256msg2(&sha, a, b));
             show(x86.sha1rnds4(&sha, a, b, 0, _));
             show(x86.sha1rnds4(&sha, a, b, 1, _));
             show(x86.sha1rnds4(&sha, a, b, 2, _));
             show(x86.sha1rnds4(&sha, a, b, 3, _));
             show(x86.sha1nexte(&sha, a, b));
             show(x86.sha1msg1(&sha, a, b));
             show(x86.sha1msg2(&sha, a, b));\n"
        ));
    }
    format!(
        "use std.cpu;
         use std.x86;
         use std.option.Option;
         use std.simd.u32x4;
         fn show(v: u32x4) -> Unit ! {{io, panic}} {{
             print_int(u32x4.lane(v, 0, _)); print_int(u32x4.lane(v, 1, _));
             print_int(u32x4.lane(v, 2, _)); print_int(u32x4.lane(v, 3, _));
         }}
         fn main() -> i64 ! {{io, panic}} {{
             let sha = match cpu.sha() {{
                 Option.Some(sha) => sha,
                 Option.None => {{ print_int(-1); return 0; }},
             }};
             {body}
             0
         }}"
    )
}

#[test]
fn the_specification_matches_the_instructions() {
    let source = program();
    let checked = check(&source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut reference = Vec::new();
    let (status, stats) = checked.evaluate_with_stats(&mut reference).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations);
    let reference = String::from_utf8(reference).unwrap();
    assert_eq!(
        reference.lines().count(),
        24 * 10 * 4,
        "the evaluator always has the token"
    );
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    {
        let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
        let binary = scratch.path().join("sha");
        let clif = kush::native::build_with_clif(&checked, &binary).unwrap();
        for routine in [
            "kush_x86_sha256rnds2",
            "kush_x86_sha1rnds4_3",
            "kush_x86_sha1msg2",
        ] {
            assert!(clif.contains(routine), "no call to {routine}");
        }
        let output = std::process::Command::new(&binary)
            .env_remove("KUSH_CPU_DISABLE")
            .output()
            .unwrap();
        assert_eq!(
            output.status.code(),
            Some(0),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let native = String::from_utf8(output.stdout).unwrap();
        if native == "-1\n" {
            eprintln!("this CPU has no SHA extensions; only the evaluator ran");
            return;
        }
        for (index, (want, got)) in reference.lines().zip(native.lines()).enumerate() {
            let names = [
                "sha256rnds2",
                "sha256msg1",
                "sha256msg2",
                "sha1rnds4 0",
                "sha1rnds4 1",
                "sha1rnds4 2",
                "sha1rnds4 3",
                "sha1nexte",
                "sha1msg1",
                "sha1msg2",
            ];
            assert_eq!(
                want,
                got,
                "{} differs (input {}, lane {})",
                names[(index / 4) % 10],
                index / 40,
                index % 4
            );
        }
        assert_eq!(reference, native);
    }
}
