// The same three kernels as ../kush/main.kush. Build twice to compare:
// `-C overflow-checks=yes` (Kush semantics) and without (Rust release default).
#[inline(never)]
fn sum(values: &[i64]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < values.len() {
        acc += values[i];
        i += 1;
    }
    acc
}

#[inline(never)]
fn dot(left: &[i64], right: &[i64]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < left.len() {
        acc += left[i] * right[i];
        i += 1;
    }
    acc
}

#[inline(never)]
fn scale(source: &[i64], target: &mut [i64], factor: i64) {
    let mut i = 0;
    while i < source.len() {
        target[i] = source[i] * factor - 7;
        i += 1;
    }
}

fn fill(n: i64, salt: i64) -> Vec<i64> {
    let mut values = Vec::with_capacity(n as usize);
    for i in 0..n {
        values.push(((i * 7919 + salt) & 4095) - 2048);
    }
    values
}

fn main() {
    let args: Vec<i64> = std::env::args()
        .skip(1)
        .map(|argument| argument.parse().unwrap_or(-1))
        .collect();
    if args.len() != 3 {
        std::process::exit(2);
    }
    let (n, repetitions, kernel) = (args[0], args[1], args[2]);
    if !(1..=8_000_000).contains(&n) || !(0..=100_000_000).contains(&repetitions) || !(0..=2).contains(&kernel) {
        std::process::exit(2);
    }
    let left = fill(n, 17);
    let right = fill(n, 4001);
    let mut scratch = fill(n, 0);
    let mut result = 0i64;
    for round in 0..repetitions {
        let step = match kernel {
            0 => sum(&left),
            1 => dot(&left, &right),
            _ => {
                scale(&left, &mut scratch, (round & 3) + 2);
                sum(&scratch)
            }
        };
        result = (result ^ step) + (round & 1);
    }
    println!("{result}");
}
