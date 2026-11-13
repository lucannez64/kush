//! Where a build's time goes, for `KUSH_TIME_PHASES=1`. Phases are summed
//! by name across the process and reported on stderr by [`report`]; when
//! the variable is unset nothing is measured.
use std::sync::{Mutex, OnceLock};
use std::time::{Duration, Instant};

static TOTALS: Mutex<Vec<(&'static str, Duration)>> = Mutex::new(Vec::new());

fn enabled() -> bool {
    static ENABLED: OnceLock<bool> = OnceLock::new();
    *ENABLED.get_or_init(|| std::env::var_os("KUSH_TIME_PHASES").is_some())
}

/// Run `work`, adding its duration to the phase `name`.
pub fn time<T>(name: &'static str, work: impl FnOnce() -> T) -> T {
    if !enabled() {
        return work();
    }
    let started = Instant::now();
    let result = work();
    add(name, started.elapsed());
    result
}

/// Add `duration` to the phase `name`.
pub fn add(name: &'static str, duration: Duration) {
    if !enabled() {
        return;
    }
    let mut totals = TOTALS
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    match totals.iter_mut().find(|(known, _)| *known == name) {
        Some((_, total)) => *total += duration,
        None => totals.push((name, duration)),
    }
}

/// Print every phase, in the order each was first measured.
pub fn report() {
    if !enabled() {
        return;
    }
    let totals = TOTALS
        .lock()
        .unwrap_or_else(|poisoned| poisoned.into_inner());
    for (name, total) in totals.iter() {
        eprintln!("phase {name}: {:.1} ms", total.as_secs_f64() * 1000.0);
    }
}
