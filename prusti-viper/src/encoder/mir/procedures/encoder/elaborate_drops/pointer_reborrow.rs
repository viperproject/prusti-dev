use crate::encoder::{errors::SpannedEncodingResult, Encoder};
use prusti_interface::environment::mir_body::borrowck::facts::{
    AllInputFacts, LocationTable, RichLocation,
};
use prusti_rustc_interface::middle::{
    mir,
    ty::{self, TyCtxt},
};

pub(super) fn add_pointer_reborrow_facts<'v, 'tcx: 'v>(
    encoder: &Encoder<'v, 'tcx>,
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &LocationTable,
    body: &mir::Body<'tcx>,
) -> SpannedEncodingResult<()> {
    let tcx = encoder.env().tcx();
    let mut lifetime_with_borrow_use = None;
    for (block, data) in body.basic_blocks.iter_enumerated() {
        match &data.terminator().kind {
            mir::TerminatorKind::Call {
                func: mir::Operand::Constant(box mir::Constant { literal, .. }),
                args,
                ..
            } => {
                if let ty::TyKind::FnDef(called_def_id, _) = literal.ty().kind() {
                    let full_called_function_name =
                        encoder.env().name.get_absolute_item_name(*called_def_id);
                    if full_called_function_name
                        == "prusti_contracts::prusti_set_lifetime_for_raw_pointer_reference_casts"
                    {
                        assert_eq!(args.len(), 1);
                        let arg = &args[0];
                        let mut statement_index = data.statements.len() - 1;
                        let argument_place = if let mir::Operand::Move(place) = arg {
                            place
                        } else {
                            unreachable!()
                        };
                        let (place, borrow_use) = loop {
                            if let Some(statement) = data.statements.get(statement_index) {
                                if let mir::StatementKind::Assign(box (target_place, rvalue)) =
                                    &statement.kind
                                {
                                    if target_place == argument_place {
                                        match rvalue {
                                            mir::Rvalue::AddressOf(_, place) => {
                                                let point_mid = location_table.location_to_point(
                                                    RichLocation::Mid(mir::Location {
                                                        block,
                                                        statement_index,
                                                    }),
                                                );
                                                let mut variable = None;
                                                for (var, point) in
                                                    &borrowck_input_facts.var_used_at
                                                {
                                                    if *point == point_mid {
                                                        assert!(variable.is_none());
                                                        variable = Some(*var);
                                                    }
                                                }
                                                let mut path = None;
                                                for (accessed_path, point) in
                                                    &borrowck_input_facts.path_accessed_at_base
                                                {
                                                    if *point == point_mid {
                                                        assert!(path.is_none());
                                                        path = Some(*accessed_path);
                                                    }
                                                }
                                                break (place, (variable.unwrap(), path.unwrap()));
                                            }
                                            _ => {
                                                unimplemented!("rvalue: {:?}", rvalue);
                                            }
                                        }
                                    }
                                }
                                statement_index -= 1;
                            } else {
                                unreachable!();
                            }
                        };
                        let ty::TyKind::Ref(reference_region, _, _) = place.ty(body, tcx).ty.kind() else {
                            unreachable!("place {place:?} must be a reference");
                        };
                        assert!(lifetime_with_borrow_use.is_none(), "the function can have only single prusti_set_lifetime_for_raw_pointer_reference_casts call");
                        lifetime_with_borrow_use = Some((*reference_region, borrow_use));
                    }
                }
            }
            _ => {}
        }
    }
    for (block, data) in body.basic_blocks.iter_enumerated() {
        for (statement_index, stmt) in data.statements.iter().enumerate() {
            if let mir::StatementKind::Assign(box (_, source)) = &stmt.kind {
                if let mir::Rvalue::Ref(reborrow_lifetime, _, place) = &source {
                    if let Some((reference_lifetime, borrow_use)) = lifetime_with_borrow_use {
                        if is_raw_pointer_deref(tcx, body, *place) {
                            add_subset_base_fact(
                                borrowck_input_facts,
                                location_table,
                                block,
                                statement_index,
                                *reborrow_lifetime,
                                reference_lifetime,
                                Some(borrow_use),
                            );
                        }
                    }
                    if let Some(reference_lifetime) = raw_pointer_reborrow(tcx, body, *place) {
                        add_subset_base_fact(
                            borrowck_input_facts,
                            location_table,
                            block,
                            statement_index,
                            *reborrow_lifetime,
                            reference_lifetime,
                            None,
                        );
                    }
                }
            }
        }
    }
    Ok(())
}

fn add_subset_base_fact(
    borrowck_input_facts: &mut AllInputFacts,
    location_table: &LocationTable,
    block: mir::BasicBlock,
    statement_index: usize,
    reborrow_lifetime: ty::Region<'_>,
    reference_lifetime: ty::Region<'_>,
    borrow_use: Option<(
        mir::Local,
        prusti_rustc_interface::dataflow::move_paths::MovePathIndex,
    )>,
) {
    let point = location_table.location_to_point(RichLocation::Mid(mir::Location {
        block,
        statement_index,
    }));
    let ty::RegionKind::ReVar(reborrow_lifetime_id) = reborrow_lifetime.kind() else {
        unreachable!("reborrow_lifetime: {:?}", reborrow_lifetime);
    };
    let ty::RegionKind::ReVar(reference_lifetime_id) = reference_lifetime.kind() else {
        unreachable!("reference_lifetime: {:?}", reference_lifetime);
    };
    borrowck_input_facts
        .subset_base
        .push((reference_lifetime_id, reborrow_lifetime_id, point));
    if let Some((variable, path)) = borrow_use {
        borrowck_input_facts.var_used_at.push((variable, point));
        borrowck_input_facts
            .path_accessed_at_base
            .push((path, point));
    }
}

fn is_raw_pointer_deref<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
) -> bool {
    let mut projections = place.iter_projections().rev();
    for (place, projection) in projections {
        if projection == mir::ProjectionElem::Deref && place.ty(body, tcx).ty.is_unsafe_ptr() {
            return true;
        }
    }
    false
}

fn raw_pointer_reborrow<'tcx>(
    tcx: TyCtxt<'tcx>,
    body: &mir::Body<'tcx>,
    place: mir::Place<'tcx>,
) -> Option<ty::Region<'tcx>> {
    let mut projections = place.iter_projections().rev();
    for (place, projection) in projections.by_ref() {
        if projection == mir::ProjectionElem::Deref && place.ty(body, tcx).ty.is_unsafe_ptr() {
            break;
        }
    }
    for (place, projection) in projections {
        if projection == mir::ProjectionElem::Deref {
            if let ty::TyKind::Ref(reference_region, _, _) = place.ty(body, tcx).ty.kind() {
                return Some(*reference_region);
            }
        }
    }
    None
}
