use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
pub fn is_function_with_body(tcx: ty::TyCtxt<'_>, def_id: DefId) -> bool {
    if let Some(trait_def_id) = tcx.trait_of_item(def_id) {
        let associated_items = tcx.associated_items(trait_def_id);
        if let Some(assoc_item) = associated_items
            .in_definition_order()
            .find(|item| item.def_id == def_id)
        {
            return assoc_item.defaultness(tcx).has_value();
        }
    }
    true
}
