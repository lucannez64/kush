fn hidden_alloc() -> Box<i64> { Box::new(7) }
fn main() { println!("{}", *hidden_alloc()); }
