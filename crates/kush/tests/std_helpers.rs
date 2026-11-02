//! Everyday standard-library helpers: byte-text search/split/replace and strict
//! numeric parsing, POSIX path helpers, integer sorting/searching, and small
//! insertion-ordered integer set/map containers. Reference and native execution
//! must agree; the reference side also asserts deterministic cleanup.

use kush::executable;
use std::io;

const SOURCE: &str = r#"
use std.result.Result;
use std.option.Option;
use std.text;
use std.path;
use std.sort;
use std.collections;

fn show(value: &Bytes) -> Unit ! {io, panic} {
    let mut i = 0;
    while i < Bytes.len(value) {
        print_i64(Bytes.get(value, i));
        i = i + 1;
    }
    print_i64(-1);
}

fn main() -> i64 ! {io, alloc, panic} {
    let sample = Bytes.from("alpha,beta,,gamma ");
    let beta = Bytes.from("beta");
    let comma = Bytes.from(",");
    let zz = Bytes.from("zz");
    print_i64(text.find(&sample, &beta));
    print_i64(text.find(&sample, &zz));
    print_i64(if text.contains(&sample, &beta) { 1 } else { 0 });
    print_i64(text.count(&sample, &comma));
    print_i64(text.split_count(&sample, 44));
    let part = match text.split_part(&sample, 44, 2) {
        Result.Ok(value) => value,
        Result.Err(code) => return code,
    };
    print_i64(Bytes.len(&part));
    drop(part);
    let part = match text.split_part(&sample, 44, 3) {
        Result.Ok(value) => value,
        Result.Err(code) => return code,
    };
    show(&part);
    drop(part);
    let bar = Bytes.from("|");
    let replaced = text.replace(sample, &comma, &bar);
    print_i64(Bytes.len(&replaced));
    print_i64(Bytes.get(&replaced, 5));
    drop(replaced);
    let padded = Bytes.from(" \tline \r\n");
    let trimmed = text.trim(&padded);
    show(&trimmed);
    drop(trimmed);
    let newline = text.trim_newline(&padded);
    print_i64(Bytes.len(&newline));
    drop(newline);
    drop(padded);
    let spaced = Bytes.from(" -1");
    match text.parse_i64(&spaced) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    drop(spaced);
    let overflow = Bytes.from("9223372036854775808");
    match text.parse_i64(&overflow) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    drop(overflow);
    let minimum_text = Bytes.from("-9223372036854775808");
    match text.parse_i64(&minimum_text) {
        Result.Ok(value) => print_i64(if value == i64.MIN { 1 } else { 0 }),
        Result.Err(code) => print_i64(-code),
    }
    drop(minimum_text);
    let too_negative = Bytes.from("-92233720368547758080");
    match text.parse_i64(&too_negative) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    drop(too_negative);
    let minimum = text.format_i64(i64.MIN);
    print_i64(Bytes.len(&minimum));
    drop(minimum);
    let negative = text.format_i64(-42);
    print_i64(Bytes.len(&negative));
    drop(negative);
    let negative_text = Bytes.from("-1");
    match text.parse_u63(&negative_text) {
        Result.Ok(_) => print_i64(-1),
        Result.Err(code) => print_i64(code),
    }
    drop(negative_text);
    let unsigned = Bytes.from("42");
    match text.parse_u63(&unsigned) {
        Result.Ok(value) => print_i64(value),
        Result.Err(code) => print_i64(-code),
    }
    drop(unsigned);
    let truth = Bytes.from("true");
    match text.parse_bool(&truth) {
        Result.Ok(value) => print_i64(if value { 1 } else { 0 }),
        Result.Err(code) => print_i64(-code),
    }
    drop(truth);
    let file_path = Bytes.from("/a/b/c.txt");
    let base = path.basename(&file_path);
    print_i64(Bytes.len(&base));
    drop(base);
    let parent = path.dirname(&file_path);
    print_i64(Bytes.get(&parent, 0));
    drop(parent);
    let suffix = path.extension(&file_path);
    print_i64(Bytes.len(&suffix));
    drop(suffix);
    let first_part = Bytes.from("/a");
    let second_part = Bytes.from("b");
    let joined = path.join(&first_part, &second_part);
    print_i64(Bytes.len(&joined));
    drop(joined);
    drop(first_part);
    drop(second_part);
    drop(file_path);
    let absolute = Bytes.from("/x");
    print_i64(if path.is_absolute(&absolute) { 1 } else { 0 });
    drop(absolute);

    let mut values = [5, 1, 4, 2, 3];
    sort.sort_i64(&mut values[..]);
    print_i64(Slice.get(&values[..], 0));
    print_i64(Slice.get(&values[..], 4));
    print_i64(sort.binary_search_i64(&values[..], 4));
    print_i64(sort.binary_search_i64(&values[..], 9));
    print_i64(if sort.is_sorted_i64(&values[..]) { 1 } else { 0 });

    let mut set_items = [0, 0, 0, 0];
    let mut set_count = 0;
    set_count = collections.set_add(&mut set_items[..], set_count, 3);
    set_count = collections.set_add(&mut set_items[..], set_count, 1);
    set_count = collections.set_add(&mut set_items[..], set_count, 3);
    print_i64(set_count);
    print_i64(if collections.set_contains(&set_items[..], set_count, 1) { 1 } else { 0 });
    set_count = collections.set_remove(&mut set_items[..], set_count, 3);
    print_i64(set_count);
    let members = collections.set_write(&set_items[..], set_count, Bytes.with_capacity(8));
    print_i64(Bytes.get(&members, 0));
    drop(members);

    let mut map_keys = [0, 0, 0, 0];
    let mut map_values = [0, 0, 0, 0];
    let mut map_count = 0;
    map_count = collections.map_set(
        &mut map_keys[..], &mut map_values[..], map_count, 1, 10,
    );
    map_count = collections.map_set(
        &mut map_keys[..], &mut map_values[..], map_count, 2, 20,
    );
    map_count = collections.map_set(
        &mut map_keys[..], &mut map_values[..], map_count, 1, 11,
    );
    print_i64(map_count);
    match collections.map_get(&map_keys[..], &map_values[..], map_count, 1) {
        Option.Some(value) => print_i64(value),
        Option.None => print_i64(-1),
    }
    match collections.map_get(&map_keys[..], &map_values[..], map_count, 9) {
        Option.Some(_) => print_i64(-1),
        Option.None => print_i64(0),
    }
    map_count = collections.map_remove(
        &mut map_keys[..], &mut map_values[..], map_count, 1,
    );
    print_i64(map_count);
    let keys = collections.map_write_keys(&map_keys[..], map_count, Bytes.with_capacity(8));
    print_i64(Bytes.get(&keys, 0));
    drop(keys);
    drop(beta);
    drop(comma);
    drop(zz);
    drop(bar);
    0
}
"#;

fn checked(source: &str) -> executable::Executable {
    let program = kush::program::load_source("<std-helpers-test>", source).unwrap();
    executable::check_program(&program)
        .unwrap_or_else(|error| panic!("{}", program.sources.render(&error)))
}

fn reference(source: &str) -> (i64, Vec<u8>) {
    let program = checked(source);
    let mut output = Vec::new();
    let (status, stats) = program
        .evaluate_with_io_and_stats(&mut io::empty(), &mut output)
        .unwrap();
    assert_eq!(stats.allocations, stats.deallocations);
    (status, output)
}

#[cfg(all(target_os = "linux", target_arch = "x86_64"))]
fn native(source: &str) -> (i64, Vec<u8>) {
    let program = checked(source);
    let scratch = kush::native::Scratch::new(&std::env::temp_dir()).unwrap();
    let binary = scratch.path().join("std-helpers");
    kush::native::build(&program, &binary).unwrap();
    let output = std::process::Command::new(&binary).output().unwrap();
    assert!(
        output.stderr.is_empty(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    (output.status.code().unwrap() as i64, output.stdout)
}

#[test]
fn text_path_sort_and_collections_match_across_backends() {
    let (status, output) = reference(SOURCE);
    assert_eq!(status, 0, "{}", String::from_utf8_lossy(&output));
    let (native_status, native_output) = native(SOURCE);
    assert_eq!(native_status, status);
    assert_eq!(native_output, output);
    let text = String::from_utf8(output).unwrap();
    // Spot-check the interesting values as well as cross-backend agreement.
    assert!(
        text.starts_with("6\n-1\n1\n3\n4\n0\n103\n97\n109\n109\n97\n32\n-1\n18\n124\n"),
        "{text}"
    );
}

#[test]
fn path_and_newline_edges_have_exact_results() {
    let source = r#"use std.text; use std.path;
        fn main() -> i64 ! {io, alloc, panic} {
            let cr = Bytes.from("a\r"); let newline = text.trim_newline(&cr);
            print_i64(Bytes.len(&newline));
            let crlf = Bytes.from("a\r\n"); let newline2 = text.trim_newline(&crlf);
            print_i64(Bytes.len(&newline2));
            let root = Bytes.from("//"); let base = path.basename(&root);
            print_i64(Bytes.len(&base)); print_i64(Bytes.get(&base, 0));
            let dotfile = Bytes.from(".bashrc"); let ext = path.extension(&dotfile);
            print_i64(Bytes.len(&ext));
            let compound = Bytes.from(".config.json"); let ext2 = path.extension(&compound);
            print_i64(Bytes.len(&ext2));
            0
        }"#;
    let (status, output) = reference(source);
    assert_eq!(status, 0);
    assert_eq!(output, b"2\n1\n1\n47\n0\n4\n");
    let (status, output) = native(source);
    assert_eq!(status, 0);
    assert_eq!(output, b"2\n1\n1\n47\n0\n4\n");
}
