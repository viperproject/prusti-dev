use super::borrowck::facts::{
    patch::apply_patch_to_borrowck,
    replace_terminator::{collect_replace_terminators, ReplaceTerminatorDesugaring},
    AllInputFacts, LocationTable,
};
use prusti_rustc_interface::middle::mir;

mod compiler;

pub use self::compiler::MirPatch;

pub fn apply_patch<'tcx>(
    patch: MirPatch<'tcx>,
    body: &mir::Body<'tcx>,
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &mut LocationTable,
) -> (mir::Body<'tcx>, Vec<ReplaceTerminatorDesugaring>) {
    let mut patched_body = body.clone();
    patch.clone().apply(&mut patched_body);
    apply_patch_to_borrowck(
        borrowck_input_facts,
        location_table,
        &patch,
        body,
        &mut patched_body,
    );
    let replace_terminators = collect_replace_terminators(body, &patched_body);
    (patched_body, replace_terminators)
}
