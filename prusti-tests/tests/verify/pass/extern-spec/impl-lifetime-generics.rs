use prusti_contracts::*;

// An extern spec on a foreign impl whose self type has a lifetime parameter:
// the spec closures are declared on a mirror of the method whose generics
// lack the impl's lifetime, so they must be instantiated with the target's
// generics kind by kind (`T` is the target's second parameter, the mirror's
// first).
#[extern_spec]
impl<'a, T> core::slice::Iter<'a, T> {
    #[pure]
    #[trusted]
    #[ensures(result.len() <= usize::MAX)]
    fn as_slice(&self) -> &'a [T];
}

fn use_as_slice(v: &[i32]) {
    let it = v.iter();
    let s = it.as_slice();
    assert!(s.len() <= usize::MAX);
}
