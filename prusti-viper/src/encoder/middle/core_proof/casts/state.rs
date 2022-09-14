use rustc_hash::FxHashSet;

#[derive(Default)]
pub(in super::super) struct CastsState {
    pub(super) encoded_casts: FxHashSet<(String, String)>,
}
