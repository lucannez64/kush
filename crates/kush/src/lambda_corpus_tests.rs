//! I-LAMBDA-INFER corpus: every lambda in the repository's example programs,
//! with all of its annotations removed. A stripped program must either check
//! and produce exactly the original result and output, or be rejected with a
//! request for the annotation. Run with `--nocapture` to see the counts.

use crate::ast;

fn lambdas<'a>(expr: &'a ast::Expr, out: &mut Vec<&'a ast::Expr>) {
    if matches!(expr.kind, ast::ExprKind::Lambda(_)) {
        out.push(expr);
    }
    crate::executable::ast_children(expr, &mut |child| lambdas(child, out));
}

fn block_lambdas<'a>(block: &'a ast::Block, out: &mut Vec<&'a ast::Expr>) {
    for statement in &block.statements {
        match statement {
            ast::Statement::Let { value, .. } | ast::Statement::Expr(value) => lambdas(value, out),
        }
    }
    if let Some(tail) = &block.tail {
        lambdas(tail, out);
    }
}

/// `fn(a: A, b: B) -> R ! {e} {` becomes `fn(a, b) {`.
fn strip(source: &str, expr: &ast::Expr) -> Option<String> {
    let ast::ExprKind::Lambda(lambda) = &expr.kind else {
        return None;
    };
    let names = lambda
        .parameters
        .iter()
        .map(|parameter| parameter.name.as_str())
        .collect::<Vec<_>>()
        .join(", ");
    let start = expr.span.start;
    let body = lambda.body.span.start;
    Some(format!(
        "{}fn({names}) {}",
        &source[..start],
        &source[body..]
    ))
}

fn outcome(source: &str) -> Result<(i64, String), String> {
    let program = crate::executable::check(source).map_err(|error| error.message)?;
    let mut output = Vec::new();
    program
        .evaluate(&mut output)
        .map(|value| (value, String::from_utf8_lossy(&output).into_owned()))
        .map_err(|error| format!("runtime: {}", error.message))
}

#[test]
fn stripped_repository_lambdas_infer_or_ask_for_annotations() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("../../examples");
    let mut files = std::fs::read_dir(&root)
        .unwrap()
        .flatten()
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|e| e == "kush"))
        .collect::<Vec<_>>();
    files.sort();
    let (mut total, mut inferred, mut asked) = (0, 0, 0);
    let mut reasons = std::collections::BTreeMap::<String, usize>::new();
    for file in files {
        let source = std::fs::read_to_string(&file).unwrap();
        let Ok(original) = outcome(&source) else {
            continue;
        };
        let module = crate::parser::parse(&source).unwrap();
        let mut found = Vec::new();
        for declaration in &module.items {
            if let ast::ItemKind::Function(function) = &declaration.item.kind
                && let Some(body) = &function.body
            {
                block_lambdas(body, &mut found);
            }
        }
        for lambda in found {
            let Some(stripped) = strip(&source, lambda) else {
                continue;
            };
            total += 1;
            match outcome(&stripped) {
                Ok(result) => {
                    assert_eq!(
                        result,
                        original,
                        "{}: a stripped lambda changed the program's result",
                        file.display()
                    );
                    inferred += 1;
                }
                Err(message) => {
                    assert!(
                        message.contains("annotate") || message.contains("type mismatch"),
                        "{}: unexpected rejection: {message}",
                        file.display()
                    );
                    let key = message
                        .split(':')
                        .next()
                        .unwrap_or_default()
                        .chars()
                        .take(60)
                        .collect::<String>();
                    *reasons.entry(key).or_default() += 1;
                    asked += 1;
                }
            }
        }
    }
    println!("lambdas: {total}, inferred: {inferred}, annotation requested: {asked}");
    println!("{reasons:#?}");
    assert!(total >= 10, "{total}");
    assert!(inferred > 0);
}
