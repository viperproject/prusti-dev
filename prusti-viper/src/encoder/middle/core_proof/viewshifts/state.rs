use rustc_hash::{FxHashMap, FxHashSet};
use vir_crate::low::{self as vir_low};

pub(super) type ViewShiftSignature = (String, Vec<vir_low::Type>);
pub(super) type ViewShiftBody = (Vec<vir_low::Expression>, Vec<vir_low::Expression>);

#[derive(Default)]
pub(in super::super) struct ViewShiftsState {
    pub(super) encoded_view_shifts: FxHashSet<ViewShiftSignature>,
    /// Used to debug assert that signature uniquely identifies the viewshift.
    pub(super) encoded_view_content: FxHashMap<ViewShiftSignature, ViewShiftBody>,
}
