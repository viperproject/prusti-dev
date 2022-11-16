//! Source: http://smallcultfollowing.com/babysteps/blog/2018/06/15/mir-based-borrow-check-nll-status-update/

fn some_condition<T>(r: &T) -> bool {
    true
}

fn foo<T>(vec: &mut Vec<T>, x: T) -> &T {
    let r = &vec[0];
    if some_condition(r) {
        return r;
    }

    // Question: can we mutate `vec` here? On Nightly,
    // you get an error, because a reference that is returned (like `r`)
    // is considered to be in scope until the end of the function,
    // even if that return only happens conditionally. Polonius can
    // accept this code.
    vec.push(x);
    let last = vec.len() - 1;
    &vec[last]
}
