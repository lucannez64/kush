fn main() { let values = vec![1i64]; let view = &values[..]; drop(values); println!("{}", view[0]); }
