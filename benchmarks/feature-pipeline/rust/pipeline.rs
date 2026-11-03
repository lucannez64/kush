// The sealed constructor enforces this particular whitelist in safe Rust.
// It does not offer Kush's general dependent, kernel-checked proposition API.
pub struct AuthorizedKey(i64);
impl AuthorizedKey {
    pub fn standard() -> Self {
        Self(23130)
    }
}

// A ZST transports no audit payload. Rust does not count syntactic value uses.
pub struct Audit;

#[must_use = "finish the batch ticket"]
pub struct Ticket {
    key: Box<i64>,
    finished: bool,
}
impl Drop for Ticket {
    fn drop(&mut self) {
        // Safe Rust is affine. A drop guard enforces this application's
        // finalization protocol at runtime, not compile time. mem::forget can
        // still bypass it; this is documented and tested as a limitation.
        assert!(self.finished, "batch ticket was not finished");
    }
}
pub fn issue(key: AuthorizedKey, _: Audit) -> Ticket {
    Ticket {
        key: Box::new(key.0),
        finished: false,
    }
}
pub fn scrub(x: i64) -> i64 {
    (x & 65535) ^ (x & 255)
}
pub fn tag(x: i64) -> i64 {
    x ^ 23130
}

pub fn fused(mut values: Vec<i64>) -> Vec<i64> {
    for value in &mut values {
        *value = tag(scrub(*value));
    }
    values
}
pub fn staged(mut values: Vec<i64>) -> Vec<i64> {
    for value in &mut values {
        *value = scrub(*value);
    }
    for value in &mut values {
        *value = tag(*value);
    }
    values
}
pub fn iterators(values: Vec<i64>) -> Vec<i64> {
    values.into_iter().map(scrub).map(tag).collect()
}
pub fn checksum(values: &[i64]) -> i64 {
    let mut sum = 0i64;
    let mut i = 0;
    while i < values.len() {
        sum += values[i];
        i += 1;
    }
    sum
}
pub fn finish(mut ticket: Ticket, sum: i64) -> i64 {
    let key = *ticket.key;
    ticket.finished = true;
    sum + key
}
pub fn batch(n: usize, mode: i64) -> i64 {
    let ticket = issue(AuthorizedKey::standard(), Audit);
    let mut values = Vec::with_capacity(n);
    for i in 0..n {
        values.push((i as i64) & 65535);
    }
    let transformed = match mode {
        0 => staged(values),
        1 => fused(values),
        _ => iterators(values),
    };
    let view = &transformed[..];
    let sum = checksum(view);
    finish(ticket, sum)
}
