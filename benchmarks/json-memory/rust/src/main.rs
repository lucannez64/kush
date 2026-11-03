use std::io::Write;
unsafe extern "C" {
    fn memory_begin();
    fn memory_stage(stage: i64);
    fn memory_end();
}
struct Seed {
    revision: i64,
    text: Vec<u8>,
    children: Vec<i64>,
}
struct Node {
    id: i64,
    revision: i64,
}
#[cfg(not(feature = "inline-metadata"))]
type Metadata = Box<Node>;
#[cfg(feature = "inline-metadata")]
type Metadata = Node;
fn metadata(node: Node) -> Metadata {
    #[cfg(not(feature = "inline-metadata"))]
    {
        Box::new(node)
    }
    #[cfg(feature = "inline-metadata")]
    {
        node
    }
}
fn replace_metadata(target: &mut Metadata, node: Node) {
    #[cfg(not(feature = "inline-metadata"))]
    {
        **target = node;
    }
    #[cfg(feature = "inline-metadata")]
    {
        *target = node;
    }
}
struct Document {
    node: Metadata,
    text: Vec<u8>,
    children: Vec<i64>,
}
fn seed() -> Seed {
    let value: serde_json::Value =
        serde_json::from_slice(include_bytes!("../../seed.json")).unwrap();
    Seed {
        revision: value["revision"].as_i64().unwrap(),
        text: value["text"].as_str().unwrap().as_bytes().to_vec(),
        children: value["children"]
            .as_array()
            .unwrap()
            .iter()
            .map(|n| n.as_i64().unwrap())
            .collect(),
    }
}
fn corpus(count: usize, initial: &Seed) -> Vec<Document> {
    let mut result = Vec::with_capacity(count);
    for id in 0..count {
        result.push(Document {
            node: metadata(Node {
                id: id as i64,
                revision: initial.revision,
            }),
            text: initial.text.clone(),
            children: initial.children.clone(),
        });
    }
    result
}
fn content(out: &mut Vec<u8>, id: i64, revision: i64) {
    let size = if revision % 2 == 1 { 512 } else { 16 };
    for i in 0..size {
        out.push((65 + (id + revision + i) % 26) as u8);
    }
}
fn subtree(out: &mut Vec<i64>, id: i64, revision: i64) {
    let size = if revision % 2 == 1 { 32 } else { 4 };
    for i in 0..size {
        out.push(id + revision + i);
    }
}
fn rebuild(doc: &mut Document) {
    let id = doc.node.id;
    let revision = doc.node.revision + 1;
    let mut text = Vec::with_capacity(16);
    content(&mut text, id, revision);
    let mut children = Vec::with_capacity(4);
    subtree(&mut children, id, revision);
    let node = metadata(Node { id, revision });
    // Construct every replacement before releasing any old field, matching Kush.
    let old = std::mem::replace(
        doc,
        Document {
            node,
            text,
            children,
        },
    );
    drop(old);
}
fn reuse(doc: &mut Document) {
    let id = doc.node.id;
    let revision = doc.node.revision + 1;
    doc.text.clear();
    doc.text.reserve(if revision % 2 == 1 { 512 } else { 16 });
    content(&mut doc.text, id, revision);
    doc.children.clear();
    doc.children.reserve(if revision % 2 == 1 { 32 } else { 4 });
    subtree(&mut doc.children, id, revision);
    replace_metadata(&mut doc.node, Node { id, revision });
}
fn number(out: &mut Vec<u8>, value: i64) {
    // Same positive-integer decimal algorithm as Kush's format_i64_into.
    assert!(value >= 0);
    let mut divisor = 1;
    let mut rest = value;
    while rest >= 10 {
        rest /= 10;
        divisor *= 10;
    }
    let mut value = value;
    while divisor > 0 {
        let digit = value / divisor;
        out.push((48 + digit) as u8);
        value -= digit * divisor;
        divisor /= 10;
    }
}
fn serialize(doc: Document) -> Vec<u8> {
    let mut out = Vec::with_capacity(128 + doc.text.len() + doc.children.len() * 24);
    out.extend_from_slice(b"{\"id\":");
    number(&mut out, doc.node.id);
    out.extend_from_slice(b",\"revision\":");
    number(&mut out, doc.node.revision);
    out.extend_from_slice(b",\"text\":\"");
    out.extend_from_slice(&doc.text);
    out.extend_from_slice(b"\",\"children\":[");
    for (index, child) in doc.children.iter().enumerate() {
        if index != 0 {
            out.push(b',');
        }
        number(&mut out, *child);
    }
    out.extend_from_slice(b"]}");
    out
}
fn consume(documents: Vec<Document>, emit: bool) -> i64 {
    let mut sum = 0;
    for doc in documents {
        let mut out = serialize(doc);
        let mut hash = 0i64;
        for &byte in &out {
            hash = (hash * 131 + i64::from(byte)) % 1_000_000_007;
        }
        if emit {
            out.push(b'\n');
            std::io::stdout().write_all(&out).unwrap();
        }
        sum += hash;
    }
    sum
}
fn main() {
    let arguments: Vec<i64> = std::env::args()
        .skip(1)
        .map(|s| s.parse().unwrap_or(-1))
        .collect();
    if arguments.len() != 4 {
        std::process::exit(2);
    }
    let (count, rounds, mode, emit) = (arguments[0], arguments[1], arguments[2], arguments[3]);
    drop(arguments);
    if !(1..=32768).contains(&count)
        || !(0..=63).contains(&rounds)
        || !(0..=1).contains(&mode)
        || !(0..=1).contains(&emit)
    {
        std::process::exit(2);
    }
    // Safety: probe functions are linked from this benchmark's fixed C object;
    // signatures use only the C ABI and no pointers cross the boundary.
    unsafe {
        memory_begin();
    }
    let initial = seed();
    let mut documents = corpus(count as usize, &initial);
    unsafe {
        memory_stage(1);
    }
    for _ in 0..rounds {
        for doc in &mut documents {
            if mode == 1 { reuse(doc) } else { rebuild(doc) }
        }
    }
    unsafe {
        memory_stage(2);
    }
    let sum = consume(documents, emit == 1);
    unsafe {
        memory_stage(3);
    }
    let small = corpus(16, &initial);
    unsafe {
        memory_stage(4);
    }
    let sum = sum + consume(small, emit == 1);
    drop(initial);
    unsafe {
        memory_end();
    }
    println!("{sum}");
}
