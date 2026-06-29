fn reborrow<U>(x: &mut U) -> &mut U {
    x
}

fn caller<T>(mut v: T) {
    let _ = reborrow(&mut v);
}
