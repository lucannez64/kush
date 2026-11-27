//! STD-BINCODE: `std.bincode` against byte-exact bincode 1.x "legacy" vectors
//! (little-endian fixed-width integers, u64 length prefixes) computed in Rust
//! with `to_le_bytes`, plus encode→decode round trips and malformed-input
//! errors. Both backends must agree and the evaluator must free every
//! allocation.
use kush::executable::check;

fn reference(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let mut output = Vec::new();
    let (status, stats) = program.evaluate_with_stats(&mut output).unwrap();
    assert_eq!(status, 0);
    assert_eq!(stats.allocations, stats.deallocations, "cleanup");
    String::from_utf8(output).unwrap()
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> String {
    let program = check(source).unwrap_or_else(|error| panic!("{error:?}"));
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("bincode");
    kush::native::build(&program, &binary).unwrap();
    let native = std::process::Command::new(&binary).output().unwrap();
    assert_eq!(native.status.code(), Some(0));
    String::from_utf8(native.stdout).unwrap()
}

fn agrees(source: &str) -> String {
    let output = reference(source);
    #[cfg(all(target_os = "linux", target_arch = "x86_64"))]
    assert_eq!(native(source), output);
    output
}

/// Render bytes the way the Kush programs print them: one decimal per line.
fn lines(bytes: &[u8]) -> String {
    bytes.iter().map(|b| format!("{b}\n")).collect()
}

/// Every scalar and container primitive, encoded and printed as bytes. The
/// expected vector is the bincode 1.3 default wire format.
#[test]
fn matches_bincode_legacy_wire_format() {
    let output = agrees(
        r#"use std.option.Option;
          use std.result.Result;
          use std.bincode;
          fn main() -> i64 ! {io, alloc} {
              let mut b = Bytes.with_capacity(128);
              b = bincode.put_u8(b, 42);
              b = bincode.put_i8(b, -5);
              b = bincode.put_u16(b, 0x0201);
              b = bincode.put_i16(b, -2);
              b = bincode.put_u32(b, 0x04030201);
              b = bincode.put_i32(b, -3);
              b = bincode.put_u64(b, 0x0807060504030201);
              b = bincode.put_i64(b, -1);
              b = bincode.put_bool(b, true);
              b = bincode.put_bool(b, false);
              b = bincode.put_char(b, 'a');
              b = bincode.put_char(b, 'é');
              let s = "hi";
              b = bincode.put_str(b, s.as_str());
              b = bincode.put_bytes(b, &Bytes.from("abc"));
              b = bincode.put_len(b, 3);
              b = bincode.put_u16(b, 1);
              b = bincode.put_u16(b, 2);
              b = bincode.put_u16(b, 3);
              b = bincode.put_variant(b, 2);
              let some: Option<u8> = Option.Some(7);
              b = bincode.put_option(b, some, fn(out: Bytes, x: u8) -> Bytes ! {alloc} { bincode.put_u8(out, x) });
              let none: Option<u8> = Option.None;
              b = bincode.put_option(b, none, fn(out: Bytes, x: u8) -> Bytes ! {alloc} { bincode.put_u8(out, x) });
              let ok: Result<u16, u8> = Result.Ok(9);
              b = bincode.put_result(b, ok, fn(out: Bytes, x: u16) -> Bytes ! {alloc} { bincode.put_u16(out, x) }, fn(out: Bytes, e: u8) -> Bytes ! {alloc} { bincode.put_u8(out, e) });
              let mut i = 0;
              while i < Bytes.len(&b) {
                  print_i64(Bytes.get(&b, i));
                  i = i + 1;
              }
              drop(b);
              0
          }"#,
    );
    let mut e: Vec<u8> = Vec::new();
    e.push(42);
    e.push((-5i8) as u8);
    e.extend(0x0201u16.to_le_bytes());
    e.extend((-2i16).to_le_bytes());
    e.extend(0x04030201u32.to_le_bytes());
    e.extend((-3i32).to_le_bytes());
    e.extend(0x0807060504030201u64.to_le_bytes());
    e.extend((-1i64).to_le_bytes());
    e.push(1);
    e.push(0);
    e.extend(97u32.to_le_bytes()); // 'a'
    e.extend(0xE9u32.to_le_bytes()); // 'é'
    e.extend(2u64.to_le_bytes());
    e.extend(b"hi");
    e.extend(3u64.to_le_bytes());
    e.extend(b"abc");
    e.extend(3u64.to_le_bytes());
    e.extend(1u16.to_le_bytes());
    e.extend(2u16.to_le_bytes());
    e.extend(3u16.to_le_bytes());
    e.extend(2u32.to_le_bytes()); // variant index
    e.push(1);
    e.push(7); // Some(7u8)
    e.push(0); // None
    e.push(0);
    e.extend(9u16.to_le_bytes()); // Ok(9u16)
    assert_eq!(output, lines(&e));
}

/// Decode a hand-built bincode buffer field by field and print the values, then
/// check `finish` accepts exactly-consumed input.
#[test]
fn decodes_bincode_legacy_vectors() {
    let mut data: Vec<u8> = Vec::new();
    data.extend(0x04030201u32.to_le_bytes()); // u32
    data.extend(0x0807060504030201u64.to_le_bytes()); // u64
    data.extend(2u64.to_le_bytes());
    data.extend(b"hi"); // str
    data.extend(3u64.to_le_bytes());
    data.extend([9u8, 8, 7]); // bytes
    data.push(1);
    data.push(42); // Some(42u8)
    data.push(0); // None tag
    data.extend(1u32.to_le_bytes()); // variant index 1
    data.extend((-2i16).to_le_bytes()); // payload
    data.push(1);
    data.push(1); // true
    data.extend(0xE9u32.to_le_bytes()); // 'é'

    // Inline arrays are capped at 32 words including their tag word, so the
    // input arrives in chunks of 16.
    let mut decls = String::new();
    let mut fills = String::new();
    for (index, chunk) in data.chunks(16).enumerate() {
        let array = chunk
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        decls.push_str(&format!(
            "let a{index}: [i64; {}] = [{array}];\n",
            chunk.len()
        ));
        fills.push_str(&format!("b = fill(b, &a{index}[..]);\n"));
    }
    let output = agrees(&format!(
        r#"use std.result.Result;
          use std.bincode;
          fn fill(b: Bytes, a: &[i64]) -> Bytes ! {{alloc}} {{
              let mut b = b;
              let mut i = 0;
              while i < Slice.len(a) {{
                  b = Bytes.push(b, Slice.get(a, i));
                  i = i + 1;
              }}
              b
          }}
          fn run(b: &Bytes) -> Result<i64, bincode.Error> ! {{io, alloc}} {{
              let mut d = bincode.new(b);
              let a = bincode.take_u32(&mut d)?;
              print_i64(Int.convert(a));
              let n = bincode.take_u64(&mut d)?;
              print_int(n);
              let s = bincode.take_str(&mut d)?;
              print_i64(s.len());
              print_i64(String.byte_at(&s, 0));
              print_i64(String.byte_at(&s, 1));
              let raw = bincode.take_bytes(&mut d)?;
              print_i64(Bytes.len(&raw));
              print_i64(Bytes.get(&raw, 0));
              print_i64(Bytes.get(&raw, 2));
              let tag = bincode.take_tag(&mut d)?;
              print_i64(tag);
              let x = bincode.take_u8(&mut d)?;
              print_i64(Int.convert(x));
              let tag = bincode.take_tag(&mut d)?;
              print_i64(tag);
              let var = bincode.take_variant(&mut d)?;
              print_i64(Int.convert(var));
              let v = bincode.take_i16(&mut d)?;
              print_i64(Int.convert(v));
              let tag = bincode.take_tag(&mut d)?;
              print_i64(tag);
              let on = bincode.take_bool(&mut d)?;
              if on {{ print_i64(1) }} else {{ print_i64(0) }}
              let c = bincode.take_char(&mut d)?;
              print_int(Char.code(c));
              drop(s);
              drop(raw);
              match bincode.finish(&d) {{
                  Result.Ok(()) => Result.Ok(0),
                  Result.Err(e) => Result.Err(e),
              }}
          }}
          fn main() -> i64 ! {{io, alloc}} {{
              {decls}
              let mut b = Bytes.with_capacity({});
              {fills}
              match run(&b) {{
                  Result.Ok(code) => {{ drop(b); code }},
                  Result.Err(_) => {{ drop(b); 1 }},
              }}
          }}"#,
        data.len(),
        decls = decls,
        fills = fills
    ));
    let expected = [
        0x04030201i64,
        0x0807060504030201u64 as i64,
        2,
        104,
        105,
        3,
        9,
        7,
        1,
        42,
        0,
        1,
        -2,
        1,
        1,
        0xE9,
    ];
    let expected: String = expected.iter().map(|v| format!("{v}\n")).collect();
    assert_eq!(output, expected);
}

/// A user-defined record encoded and decoded with hand-written functions:
/// struct fields in order, a u64 length-prefixed Vec, and an Option tag.
#[test]
fn round_trips_a_user_record() {
    let output = agrees(
        r#"use std.option.Option;
          use std.result.Result;
          use std.bincode;
          struct Rec { id: u64, scores: Vec<i32>, note: Option<u8> }
          fn put_rec(b: Bytes, r: Rec) -> Bytes ! {alloc} {
              let Rec { id, scores, note } = r;
              let mut b = bincode.put_u64(b, id);
              b = bincode.put_len(b, Int.truncate(Vec.len(&scores)));
              let mut i = 0;
              while i < Vec.len(&scores) {
                  b = bincode.put_i32(b, Vec.get(&scores, i));
                  i = i + 1;
              }
              b = bincode.put_option(b, note, fn(out: Bytes, x: u8) -> Bytes ! {alloc} { bincode.put_u8(out, x) });
              drop(scores);
              b
          }
          fn get_rec<'a>(d: &mut bincode.Decoder<'a>) -> Result<Rec, bincode.Error> ! {alloc} {
              let id = bincode.take_u64(d)?;
              let n = bincode.take_len(d)?;
              let mut scores: Vec<i32> = Vec.with_capacity(Int.truncate(n));
              let mut i: u64 = 0;
              while i < n {
                  scores = Vec.push(scores, bincode.take_i32(d)?);
                  i = i + 1;
              }
              let tag = bincode.take_tag(d)?;
              let note: Option<u8> = if tag == 0 {
                  Option.None
              } else {
                  Option.Some(bincode.take_u8(d)?)
              };
              Result.Ok(Rec { id: id, scores: scores, note: note })
          }
          fn main() -> i64 ! {io, alloc} {
              let mut scores: Vec<i32> = Vec.new();
              scores = Vec.push(scores, -1);
              scores = Vec.push(scores, 1000000);
              scores = Vec.push(scores, 7);
              let rec = Rec { id: 0x0102030405060708, scores: scores, note: Option.Some(200) };
              let mut b = Bytes.with_capacity(64);
              b = put_rec(b, rec);
              // Same bytes as Rust bincode for (u64, Vec<i32>, Option<u8>).
              let mut i = 0;
              while i < Bytes.len(&b) {
                  print_i64(Bytes.get(&b, i));
                  i = i + 1;
              }
              let mut d = bincode.new(&b);
              let res = get_rec(&mut d);
              match res {
                  Result.Ok(back) => {
                      let Rec { id, scores, note } = back;
                      print_i64(Int.truncate(id));
                      print_i64(Vec.len(&scores));
                      print_i64(Int.convert(Vec.get(&scores, 0)));
                      print_i64(Int.convert(Vec.get(&scores, 1)));
                      print_i64(Int.convert(Vec.get(&scores, 2)));
                      match note {
                          Option.Some(x) => print_i64(Int.convert(x)),
                          Option.None => print_i64(-1),
                      }
                      let fin = bincode.finish(&d);
                      drop(scores);
                      drop(d);
                      drop(b);
                      match fin {
                          Result.Ok(()) => print_i64(0),
                          Result.Err(_) => print_i64(-1),
                      }
                      0
                  },
                  Result.Err(_) => { drop(d); drop(b); 1 },
              }
          }"#,
    );
    let mut e: Vec<u8> = Vec::new();
    e.extend(0x0102030405060708u64.to_le_bytes());
    e.extend(3u64.to_le_bytes());
    e.extend((-1i32).to_le_bytes());
    e.extend(1000000i32.to_le_bytes());
    e.extend(7i32.to_le_bytes());
    e.push(1);
    e.push(200);
    let mut expected = lines(&e);
    expected.push_str(&format!(
        "{}\n3\n-1\n1000000\n7\n200\n0\n",
        0x0102030405060708u64
    ));
    assert_eq!(output, expected);
}

/// Malformed input is an `Err`, never a panic: codes 1..6 are the Error
/// variants Truncated, BadLength, InvalidBool, InvalidChar, InvalidUtf8,
/// Trailing.
#[test]
fn reports_malformed_input() {
    let cases: [(&str, Vec<u8>); 6] = [
        ("take_u64", vec![1, 2, 3]), // truncated u64
        ("take_bytes", {
            let mut v = (1u64 << 62).to_le_bytes().to_vec(); // length > remaining
            v.push(0);
            v
        }),
        ("take_bool", vec![7]),                          // bad bool tag
        ("take_char", 0xD800u32.to_le_bytes().to_vec()), // surrogate
        ("take_str", {
            let mut v = 1u64.to_le_bytes().to_vec();
            v.push(255); // invalid UTF-8
            v
        }),
        ("finish", vec![1, 2]), // trailing bytes
    ];
    for (index, (call, data)) in cases.iter().enumerate() {
        let array = data
            .iter()
            .map(|b| b.to_string())
            .collect::<Vec<_>>()
            .join(", ");
        let read = if *call == "finish" {
            "match bincode.finish(&d) { Result.Ok(()) => print_i64(0), Result.Err(e) => print_i64(code(e)) }"
                .to_string()
        } else {
            format!(
                "match bincode.{call}(&mut d) {{ Result.Ok(_) => print_i64(0), Result.Err(e) => print_i64(code(e)) }}"
            )
        };
        let output = agrees(&format!(
            r#"use std.result.Result;
              use std.bincode;
              fn code(e: bincode.Error) -> i64 ! {{}} {{
                  match e {{
                      bincode.Error.Truncated(_) => 1,
                      bincode.Error.BadLength(_) => 2,
                      bincode.Error.InvalidBool(_) => 3,
                      bincode.Error.InvalidChar(_) => 4,
                      bincode.Error.InvalidUtf8(_) => 5,
                      bincode.Error.Trailing(_) => 6,
                  }}
              }}
              fn run(b: &Bytes) -> i64 ! {{io, alloc}} {{
                  let mut d = bincode.new(b);
                  {read}
                  0
              }}
              fn main() -> i64 ! {{io, alloc}} {{
                  let raw: [i64; {}] = [{}];
                  let mut b = Bytes.with_capacity({});
                  let mut i = 0;
                  while i < {} {{
                      b = Bytes.push(b, raw[i]);
                      i = i + 1;
                  }}
                  let r = run(&b);
                  drop(b);
                  r
              }}"#,
            data.len(),
            array,
            data.len(),
            data.len()
        ));
        let expected_code = if *call == "finish" {
            6
        } else {
            index as i64 + 1
        };
        assert_eq!(output, format!("{expected_code}\n"), "case {call}");
    }
}

/// The Truncated error carries the offset where the input ran out.
#[test]
fn truncated_error_carries_the_offset() {
    let output = agrees(
        r#"use std.result.Result;
          use std.bincode;
          fn main() -> i64 ! {io, alloc} {
              let mut b = Bytes.with_capacity(4);
              b = Bytes.push(b, 1);
              b = Bytes.push(b, 2);
              b = Bytes.push(b, 3);
              let mut d = bincode.new(&b);
              match bincode.take_u64(&mut d) {
                  Result.Ok(_) => print_i64(-1),
                  Result.Err(e) => match e {
                      bincode.Error.Truncated(at) => print_i64(at),
                      _ => print_i64(-2),
                  },
              }
              drop(d);
              drop(b);
              0
          }"#,
    );
    assert_eq!(output, "0\n");
}
