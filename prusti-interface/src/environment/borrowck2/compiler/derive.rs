//! Derive additional information from the extracted one.

use std::collections::HashMap;
use rustc_middle::{mir, ty, ty::TyCtxt};
use rustc_span::Symbol;

pub(super) fn extract_local_names<'tcx>(body: &mir::Body<'tcx>) -> HashMap<mir::Local, String> {
    let mut names = HashMap::new();
    for info in &body.var_debug_info {
        if let mir::VarDebugInfoContents::Place(place) = info.value {
            if let Some(local) = place.as_local() {
                names.insert(local, info.name.to_string());
            } else {
                unimplemented!();
            }
        } else {
            unimplemented!();
        }
    }
    names
}