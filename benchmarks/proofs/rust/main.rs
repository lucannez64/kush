// The kernels of ../kush/main.kush. The fourth argument picks the form:
// 0 is safe Rust (every index checked), 1 is unsafe Rust that skips exactly
// the checks Kush proves unnecessary. Build with `-C overflow-checks=yes`:
// the accumulators stay checked in both forms, as in Kush.
#[inline(never)]
fn sum<const TRUSTED: bool>(values: &[i64]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < values.len() {
        // SAFETY: i < values.len().
        acc += if TRUSTED { unsafe { *values.get_unchecked(i) } } else { values[i] };
        i += 1;
    }
    acc
}

#[inline(never)]
fn stencil<const TRUSTED: bool>(data: &[u8]) -> i64 {
    let mut acc = 0i64;
    let mut i = 1;
    while i < data.len() - 1 {
        let window = if TRUSTED {
            // SAFETY: 1 <= i < len - 1, and each byte is at most 255, so the
            // window is at most 1,020.
            unsafe {
                let a = *data.get_unchecked(i.unchecked_sub(1)) as i64;
                let b = *data.get_unchecked(i) as i64;
                let c = *data.get_unchecked(i.unchecked_add(1)) as i64;
                a.unchecked_add(b.unchecked_mul(2)).unchecked_add(c)
            }
        } else {
            data[i - 1] as i64 + 2 * data[i] as i64 + data[i + 1] as i64
        };
        acc += window;
        i += 1;
    }
    acc
}

fn crc_table() -> Vec<u32> {
    let mut entries = Vec::with_capacity(256);
    for n in 0..256u32 {
        let mut c = n;
        for _ in 0..8 {
            c = if c & 1 == 1 { 0xEDB8_8320 ^ (c >> 1) } else { c >> 1 };
        }
        entries.push(c);
    }
    entries
}

#[inline(never)]
fn crc32<const TRUSTED: bool>(table: &[u32], crc: u32, data: &[u8]) -> u32 {
    let mut c = crc ^ 0xFFFF_FFFF;
    let mut i = 0;
    while i < data.len() {
        // SAFETY: i < data.len(), and the table has 256 entries (checked by
        // the caller), indexed by a value masked to 0..=255.
        let byte = if TRUSTED { unsafe { *data.get_unchecked(i) } } else { data[i] } as u32;
        let index = ((c ^ byte) & 255) as usize;
        c = if TRUSTED { unsafe { *table.get_unchecked(index) } } else { table[index] } ^ (c >> 8);
        i += 1;
    }
    c ^ 0xFFFF_FFFF
}

/// A table of at least 256 entries: `new` checks it, as Kush's field type
/// promises it.
struct Codec {
    table: Vec<i64>,
}

impl Codec {
    fn new(table: Vec<i64>) -> Codec {
        assert!(table.len() >= 256);
        Codec { table }
    }
}

#[inline(never)]
fn lookup<const TRUSTED: bool>(codec: &Codec, data: &[u8]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    while i < data.len() {
        // SAFETY: i < data.len(); the table has at least 256 entries and
        // `at` is a byte.
        let at = if TRUSTED { unsafe { *data.get_unchecked(i) } } else { data[i] } as usize;
        acc += if TRUSTED { unsafe { *codec.table.get_unchecked(at) } } else { codec.table[at] };
        i += 1;
    }
    acc
}

#[inline(never)]
fn follow<const TRUSTED: bool>(values: &[i64]) -> i64 {
    let mut acc = 0i64;
    let mut i = 0;
    let mut j = 0;
    while i < values.len() {
        // SAFETY: j <= i < values.len().
        acc += if TRUSTED { unsafe { *values.get_unchecked(j) } } else { values[j] };
        if (if TRUSTED { unsafe { *values.get_unchecked(i) } } else { values[i] }) > 0 {
            j += 1;
        }
        i += 1;
    }
    acc
}

fn run<const TRUSTED: bool>(n: i64, repetitions: i64, kernel: i64) -> i64 {
    let mut values = Vec::with_capacity(n as usize);
    let mut data = Vec::with_capacity(n as usize);
    for i in 0..n {
        values.push(((i * 7919 + 17) & 4095) - 2048);
        data.push(((i * 7 + 3) & 255) as u8);
    }
    let table = crc_table();
    assert_eq!(table.len(), 256);
    let codec = Codec::new((0..256i64).map(|k| ((k * 40503 + 7) & 1023) - 512).collect());
    let mut result = 0i64;
    for round in 0..repetitions {
        let step = match kernel {
            0 => sum::<TRUSTED>(&values),
            1 => stencil::<TRUSTED>(&data),
            3 => lookup::<TRUSTED>(&codec, &data),
            4 => follow::<TRUSTED>(&values),
            _ => crc32::<TRUSTED>(&table, round as u32, &data) as i64,
        };
        result = (result ^ step) + (round & 1);
    }
    result
}

fn main() {
    let args: Vec<i64> = std::env::args()
        .skip(1)
        .map(|argument| argument.parse().unwrap_or(-1))
        .collect();
    if args.len() != 4 {
        std::process::exit(2);
    }
    let (n, repetitions, kernel, trusted) = (args[0], args[1], args[2], args[3]);
    if !(3..=8_000_000).contains(&n)
        || !(0..=100_000_000).contains(&repetitions)
        || !(0..=4).contains(&kernel)
        || !(0..=1).contains(&trusted)
    {
        std::process::exit(2);
    }
    let result = if trusted == 1 { run::<true>(n, repetitions, kernel) } else { run::<false>(n, repetitions, kernel) };
    println!("{result}");
}
