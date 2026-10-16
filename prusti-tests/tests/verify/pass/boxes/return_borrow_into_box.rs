// The boxed value's address is heap-dependent; its cast inside the wand's
// `package` must be evaluated in the labelled state.
fn deref_box(b: &mut Box<i32>) -> &mut i32 {
    &mut **b
}
