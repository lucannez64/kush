#[allow(dead_code)]
#[path = "../../rust/pipeline.rs"]
mod pipeline;
fn main() { let ticket = pipeline::issue(pipeline::AuthorizedKey::standard(), pipeline::Audit); std::mem::forget(ticket); }
