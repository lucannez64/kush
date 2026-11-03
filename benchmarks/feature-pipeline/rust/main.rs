#[cfg(instrument)]
mod allocation;
mod pipeline;

fn main() {
    let args = std::env::args().skip(1).collect::<Vec<_>>();
    if args.len() != 3 {
        std::process::exit(2);
    }
    let parsed = args
        .iter()
        .map(|s| s.parse::<i64>())
        .collect::<Result<Vec<_>, _>>();
    let Ok(config) = parsed else {
        std::process::exit(2);
    };
    let (n, rounds, mode) = (config[0], config[1], config[2]);
    if !(1..=8_000_000).contains(&n) || !(0..=32).contains(&rounds) || !(0..=2).contains(&mode) {
        std::process::exit(2);
    }
    #[cfg(instrument)]
    allocation::start();
    let mut result = 0i64;
    for _ in 0..rounds {
        result += pipeline::batch(n as usize, mode);
    }
    #[cfg(instrument)]
    allocation::stop();
    println!("{result}");
    #[cfg(instrument)]
    allocation::report();
}
