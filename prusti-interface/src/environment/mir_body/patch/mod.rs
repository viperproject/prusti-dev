use super::borrowck::facts::{patch::apply_patch_to_borrowck, AllInputFacts, LocationTable};
use rustc_middle::mir;

mod compiler;
mod fixer;

pub use self::compiler::MirPatch;

pub fn apply_patch<'tcx>(
    patch: MirPatch<'tcx>,
    body: &mir::Body<'tcx>,
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
) -> mir::Body<'tcx> {
    let patch = self::fixer::fix_patch(body, patch);
    let mut patched_body = body.clone();
    patch.clone().apply(&mut patched_body);
    apply_patch_to_borrowck(
        borrowck_input_facts,
        location_table,
        &patch,
        body,
        &patched_body,
    );
    patched_body
}
