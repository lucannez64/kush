//! The LLVM backend's `noalias` facts and the replay of deferred loops rest
//! on a written view sharing no element with any other live view. These are
//! the ways one might try to get such a pair; the checker must refuse each.
use kush::executable;

const HELPERS: &str = "
fn f<'a, 'b>(source: &'a [i64], target: &'b mut [i64]) -> Unit ! {panic} {
    let mut i = 0;
    while i < Slice.len(source) {
        Slice.set(target, i, Slice.get(source, i) * 3);
        i = i + 1;
    }
}
fn g<'a, 'b>(one: &'a mut [i64], two: &'b mut [i64]) -> Unit ! {panic} {
    Slice.set(one, 0, Slice.get(two, 0));
}
fn id<'a>(x: &'a mut [i64]) -> &'a mut [i64] ! {} { x }
";

fn rejected(body: &str) {
    let source = format!(
        "{HELPERS}
        fn main() -> Unit ! {{io, panic}} {{
            let mut v: [i64; 8] = [1, 2, 3, 4, 5, 6, 7, 8];
            {body}
            print_i64(v[0]);
        }}"
    );
    assert!(
        executable::check(&source).is_err(),
        "accepted an aliasing pair:\n{body}"
    );
}

#[test]
fn a_written_view_never_shares_elements_with_another_view() {
    // Shared and exclusive views of one owner in one call.
    rejected("f(&v[..], &mut v[..]);");
    rejected("g(&mut v[..], &mut v[..]);");
    // Overlapping, and even disjoint, ranges of one owner.
    rejected("f(&v[2..6], &mut v[0..4]);");
    rejected("f(&v[0..4], &mut v[4..8]);");
    // Views kept in locals.
    rejected("let a = &mut v[..]; let b = &v[..]; f(b, a);");
    rejected("let a = &v[..]; f(a, &mut v[..]); print_i64(Slice.get(a, 0));");
    // A view returned by a function still borrows its owner.
    rejected("let a = id(&mut v[..]); f(&v[..], a);");
    rejected("let a = &mut v[..]; let b = id(a); let c = &v[..]; f(c, b);");
    // Views of a view.
    rejected("let a = &mut v[..]; let b = &mut a[0..4]; let c = &a[2..6]; f(c, b);");
    rejected("let a = &mut v[..]; let b = &a[..]; f(b, a);");
}

#[test]
fn slice_views_do_not_cross_the_foreign_boundary() {
    for parameter in ["&mut [i64]", "&[i64]"] {
        let source = format!(
            "foreign \"ext\" fn ext(x: {parameter}) -> i64 ! {{io}};
            fn main() -> Unit ! {{io, panic}} {{
                let mut v: [i64; 2] = [1, 2];
                print_i64(ext(&mut v[..]));
            }}"
        );
        let Err(error) = executable::check(&source) else {
            panic!("accepted a foreign parameter of type {parameter}");
        };
        let error = format!("{error:?}");
        assert!(
            error.contains("not part of the stable C bridge ABI"),
            "{error}"
        );
    }
}
