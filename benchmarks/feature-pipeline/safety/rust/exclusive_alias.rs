fn main() { let mut values = [1i64, 2]; let a = &mut values[..]; let b = &mut values[..]; a[0] = 3; println!("{}", b[0]); }
