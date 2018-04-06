// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::{self, TyCtxt, Ty, TypeVariants, TypeFlags};
use rustc::mir;
use rustc_data_structures::indexed_vec::Idx;
use utils::type_visitor::{self, TypeVisitor};

use prusti_interface::environment::{ProcedureImpl, Procedure};


#[derive(Debug)]
pub struct BorrowInfo<'tcx> {
    /// Region of this borrow.
    region: ty::BoundRegion,
    blocking_paths: Vec<mir::Place<'tcx>>,
    blocked_paths: Vec<mir::Place<'tcx>>,
    //blocked_lifetimes: Vec<String>, TODO: Get this info from the constraints graph.
}

impl<'tcx> BorrowInfo<'tcx> {

    fn new(region: ty::BoundRegion) -> Self {
        BorrowInfo {
            region: region,
            blocking_paths: Vec::new(),
            blocked_paths: Vec::new(),
        }
    }

}

pub struct BorrowInfoCollectingVisitor<'a, 'tcx: 'a> {
    borrow_infos: Vec<BorrowInfo<'tcx>>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    /// Can the currently analysed path block other paths? For return
    /// type this is initially true, and for parameters it is true below
    /// the first reference.
    is_path_blocking: bool,
    current_path: Option<mir::Place<'tcx>>,
}

impl<'a, 'tcx> BorrowInfoCollectingVisitor<'a, 'tcx> {

    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        BorrowInfoCollectingVisitor {
            borrow_infos: Vec::new(),
            tcx: tcx,
            is_path_blocking: false,
            current_path: None,
        }
    }

    fn analyse_return_ty(&mut self, ty: Ty<'tcx>) {
        self.is_path_blocking = true;
        self.current_path = Some(mir::Place::Local(mir::RETURN_PLACE));
        self.visit_ty(ty);
        self.current_path = None;
    }

    fn analyse_arg(&mut self, arg: mir::Local, ty: Ty<'tcx>) {
        self.is_path_blocking = false;
        self.current_path = Some(mir::Place::Local(arg));
        self.visit_ty(ty);
        self.current_path = None;
    }

    fn extract_bound_region(&self, region: ty::Region<'tcx>) -> ty::BoundRegion {
        match region {
            &ty::RegionKind::ReFree(free_region) => free_region.bound_region,
            _ => unimplemented!(),
        }
    }

    fn get_or_create_borrow_info(&mut self, region: ty::BoundRegion) -> &mut BorrowInfo<'tcx> {
        if let Some(index) = self.borrow_infos.iter().position(|info| info.region == region) {
            &mut self.borrow_infos[index]
        } else {
            let borrow_info = BorrowInfo::new(region);
            self.borrow_infos.push(borrow_info);
            self.borrow_infos.last_mut().unwrap()
        }
    }

}

impl<'a, 'tcx> TypeVisitor<'a, 'tcx> for BorrowInfoCollectingVisitor<'a, 'tcx> {

    fn tcx(&self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.tcx
    }

    fn visit_field(&mut self, index: usize, field: &ty::FieldDef, substs: &'tcx ty::subst::Substs<'tcx>) {
        trace!("visit_field({}, {:?})", index, field);
        let old_path = self.current_path.take().unwrap();
        let ty = field.ty(self.tcx(), substs);
        let field_id = mir::Field::new(index);
        self.current_path = Some(old_path.clone().field(field_id, ty));
        type_visitor::walk_field(self, field, substs);
        self.current_path = Some(old_path);
    }

    fn visit_ref(&mut self, region: ty::Region<'tcx>, tym: ty::TypeAndMut<'tcx>) {
        trace!("visit_ref({:?}, {:?}) current_path={:?}", region, tym, self.current_path);
        let bound_region = self.extract_bound_region(region);
        let is_path_blocking = self.is_path_blocking;
        let old_path = self.current_path.take().unwrap();
        let current_path = old_path.clone().deref();
        self.current_path = Some(current_path.clone());
        let borrow_info = self.get_or_create_borrow_info(bound_region);
        if is_path_blocking {
            borrow_info.blocking_paths.push(current_path);
        } else {
            borrow_info.blocked_paths.push(current_path);
        }
        self.is_path_blocking = true;
        type_visitor::walk_ref(self, region, tym);
        self.is_path_blocking = is_path_blocking;
        self.current_path = Some(old_path);
    }

}

pub fn compute_borrow_infos<'p, 'a, 'tcx>(
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Vec<BorrowInfo<'tcx>>
    where
        'a: 'p,
        'tcx: 'a
{
    trace!("[compute_borrow_infos] enter name={}", procedure.get_name());
    let mir = procedure.get_mir();
    let return_ty = mir.return_ty();
    let mut visitor = BorrowInfoCollectingVisitor::new(tcx);
    for arg in mir.args_iter() {
        let arg_decl = &mir.local_decls[arg];
        visitor.analyse_arg(arg, arg_decl.ty);
    }
    visitor.analyse_return_ty(return_ty);
    let borrow_infos: Vec<_> = visitor
        .borrow_infos;
        //.into_iter()
        //.filter(|info| !info.blocked_paths.is_empty())
        //.collect();
    for borrow_info in borrow_infos.iter() {
        debug!("borrow_info: {:?}", borrow_info);
    }
    trace!("[compute_borrow_infos] exit");
    borrow_infos
}
