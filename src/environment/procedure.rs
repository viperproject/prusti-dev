// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::{self, Ty, TyCtxt};
use rustc::hir::def_id::DefId;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Procedure as ProcedureSpec;
use std::collections::HashSet;
use rustc::mir::Mir;
use std::cell::Ref;
use rustc::mir::BasicBlock;
use rustc::mir::BasicBlockData;

pub struct Procedure<'a, 'tcx: 'a> {
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    proc_def_id: ProcedureDefId,
    mir: Ref<'a, Mir<'tcx>>,
    spec_basic_blocks: HashSet<BasicBlock>,
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

fn build_spec_basic_blocks<'tcx>(mir: &Mir<'tcx>) -> HashSet<BasicBlock> {
    unimplemented!();
}

impl<'a, 'tcx> Procedure<'a, 'tcx> {
    pub fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>, proc_def_id: ProcedureDefId) -> Self {
        let mir = tcx.mir_validated(proc_def_id).borrow();
        let spec_basic_blocks = build_spec_basic_blocks(&mir);
        Procedure { tcx, proc_def_id, mir, spec_basic_blocks }
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

    fn walk_once_raw_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlock, &BasicBlockData) {
        let basic_blocks = self.mir.basic_blocks();
        for bbi in basic_blocks.indices() {
            let bb_data = &basic_blocks[bbi];
            visitor(bbi, bb_data);
        }
    }

    fn walk_once_cfg<F>(&self, mut visitor: F) where F: FnMut(BasicBlock, &BasicBlockData) {
        let basic_blocks = self.mir.basic_blocks();
        for bbi in basic_blocks.indices() {
            if !self.spec_basic_blocks.contains(&bbi) {
                let bb_data = &basic_blocks[bbi];
                visitor(bbi, bb_data);
            }
        }
    }
}
