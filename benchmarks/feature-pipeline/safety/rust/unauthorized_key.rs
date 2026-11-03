#[allow(dead_code)]
#[path = "../../rust/pipeline.rs"]
mod pipeline;
fn main() { let _ = pipeline::issue(pipeline::AuthorizedKey(0), pipeline::Audit); }
