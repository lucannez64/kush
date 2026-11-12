#!/usr/bin/env python3
"""Generate one synthetic program in Kush and in Rust, of a chosen size.

Each unit is seven small functions (a checked reduction, an element-wise
kernel, a vector fill, branchy scalar code, a recursion, a search and a
driver) with constants that differ per unit, so nothing is shared between
units. `main` runs every unit once and prints one checksum, which must be
the same for both languages. The point is build time on a program larger
than the other benchmarks, not run time.
"""
import argparse
from pathlib import Path


def kush_unit(u):
    a, b, c = 3 + u % 7, 11 + u % 13, 5 + u % 5
    return f"""
#[noalloc]
fn sum_{u}(values: &[i64]) -> i64 ! {{panic}} {{
    let mut acc = {u};
    let mut i = 0;
    while i < Slice.len(values) {{
        acc = acc + Slice.get(values, i) * {a};
        i = i + 1;
    }}
    acc
}}

#[noalloc]
fn scale_{u}<'a, 'b>(source: &'a [i64], target: &'b mut [i64], factor: i64) -> Unit ! {{panic}} {{
    let mut i = 0;
    while i < Slice.len(source) {{
        Slice.set(target, i, Slice.get(source, i) * factor - {b});
        i = i + 1;
    }}
}}

fn fill_{u}(n: i64) -> Vec<i64> ! {{alloc, panic}} {{
    let mut values: Vec<i64> = Vec.with_capacity(n);
    let mut i = 0;
    while i < n {{
        values = Vec.push(values, ((i * {7919 + 2 * u} + {u}) & 1023) - 512);
        i = i + 1;
    }}
    values
}}

#[noalloc]
fn pick_{u}(x: i64, y: i64) -> i64 ! {{panic}} {{
    if x < y {{
        if x & 1 == 0 {{ x * {a} + y }} else {{ y - x * {c} }}
    }} else {{
        if y > {b} {{ (x - y) * {c} }} else {{ x + y + {u} }}
    }}
}}

#[noalloc]
fn climb_{u}(n: i64, acc: i64) -> i64 ! {{panic}} {{
    if n == 0 {{ acc }} else {{ climb_{u}(n - 1, acc + pick_{u}(n, acc & 63)) }}
}}

#[noalloc]
fn find_{u}(values: &[i64], wanted: i64) -> i64 ! {{panic}} {{
    let mut i = 0;
    let mut at = 0 - 1;
    while i < Slice.len(values) {{
        if Slice.get(values, i) == wanted {{ at = i; break; }}
        i = i + 1;
    }}
    at
}}

fn unit_{u}() -> i64 ! {{alloc, panic}} {{
    let source = fill_{u}({64 + u % 32});
    let mut target = fill_{u}({64 + u % 32});
    scale_{u}(&source[..], &mut target[..], {c});
    let found = find_{u}(&source[..], {(u * 37) % 512 - 256});
    sum_{u}(&target[..]) + climb_{u}({20 + u % 9}, {u}) + found
}}
"""


def rust_unit(u):
    a, b, c = 3 + u % 7, 11 + u % 13, 5 + u % 5
    return f"""
fn sum_{u}(values: &[i64]) -> i64 {{
    let mut acc: i64 = {u};
    let mut i = 0;
    while i < values.len() {{
        acc = acc + values[i] * {a};
        i += 1;
    }}
    acc
}}

fn scale_{u}(source: &[i64], target: &mut [i64], factor: i64) {{
    let mut i = 0;
    while i < source.len() {{
        target[i] = source[i] * factor - {b};
        i += 1;
    }}
}}

fn fill_{u}(n: i64) -> Vec<i64> {{
    let mut values: Vec<i64> = Vec::with_capacity(n as usize);
    let mut i: i64 = 0;
    while i < n {{
        values.push(((i * {7919 + 2 * u} + {u}) & 1023) - 512);
        i += 1;
    }}
    values
}}

fn pick_{u}(x: i64, y: i64) -> i64 {{
    if x < y {{
        if x & 1 == 0 {{ x * {a} + y }} else {{ y - x * {c} }}
    }} else {{
        if y > {b} {{ (x - y) * {c} }} else {{ x + y + {u} }}
    }}
}}

fn climb_{u}(n: i64, acc: i64) -> i64 {{
    if n == 0 {{ acc }} else {{ climb_{u}(n - 1, acc + pick_{u}(n, acc & 63)) }}
}}

fn find_{u}(values: &[i64], wanted: i64) -> i64 {{
    let mut i = 0;
    let mut at: i64 = -1;
    while i < values.len() {{
        if values[i] == wanted {{ at = i as i64; break; }}
        i += 1;
    }}
    at
}}

fn unit_{u}() -> i64 {{
    let source = fill_{u}({64 + u % 32});
    let mut target = fill_{u}({64 + u % 32});
    scale_{u}(&source[..], &mut target[..], {c});
    let found = find_{u}(&source[..], {(u * 37) % 512 - 256});
    sum_{u}(&target[..]) + climb_{u}({20 + u % 9}, {u}) + found
}}
"""


def kush_program(units):
    body = "".join(kush_unit(u) for u in range(units))
    calls = "\n".join(f"    result = (result ^ unit_{u}()) + {u & 1};" for u in range(units))
    return f"""module build_scale;
{body}
fn main() -> i64 ! {{io, alloc, panic}} {{
    let mut result = 0;
{calls}
    print_i64(result);
    0
}}
"""


def rust_program(units):
    body = "".join(rust_unit(u) for u in range(units))
    calls = "\n".join(f"    result = (result ^ unit_{u}()) + {u & 1};" for u in range(units))
    return f"""{body}
fn main() {{
    let mut result: i64 = 0;
{calls}
    println!("{{result}}");
}}
"""


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("units", type=int)
    parser.add_argument("directory", type=Path)
    args = parser.parse_args()
    args.directory.mkdir(parents=True, exist_ok=True)
    (args.directory / "main.kush").write_text(kush_program(args.units))
    (args.directory / "main.rs").write_text(rust_program(args.units))


if __name__ == "__main__":
    main()
