// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Procedure as ProcedureSpec;
use std::collections::HashSet;
use rustc::mir::Mir;
use prusti_interface::environment::OnceCFGVisitor;
use std::cell::Ref;

pub struct Procedure<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Ref<'a, Mir<'tcx>>,
}

fn get_type_def_id<'tcx>(ty: Ty<'tcx>) -> Option<DefId> {
    match ty.sty {
        ty::TyAdt(def, _) => Some(def.did),
        _ => None
    }
}

fn clean_type<'a, 'gcx, 'tcx>(tcx: TyCtxt<'a, 'gcx, 'tcx>, ty: Ty<'tcx>) -> Ty<'tcx> {
    match get_type_def_id(ty) {
        Some(def_id) => tcx.type_of(def_id),
        None => ty
    }
}

impl<'a, 'tcx> Procedure<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, proc_def_id: ProcedureDefId) -> Self {
        let mir = tcx.mir_validated(proc_def_id).borrow();
        Procedure { tcx, proc_def_id, mir }
    }

    pub fn get_declared_types(&self) -> Vec<Ty<'tcx>> {
        let mut types: HashSet<Ty> = HashSet::new();
        for var in &self.mir.local_decls {
            for ty in var.ty.walk() {
                let declared_ty = ty;
                //let declared_ty = clean_type(tcx, ty);
                //let declared_ty = tcx.erase_regions(&ty);
                types.insert(declared_ty);
            }
        }
        types.into_iter().collect()
    }
}

impl<'a, 'tcx> ProcedureSpec for Procedure<'a, 'tcx> {
    fn get_id(&self) -> ProcedureDefId { self.proc_def_id }

    fn walk_once(&self, visitor: &mut OnceCFGVisitor)  { unimplemented!(); }
}
