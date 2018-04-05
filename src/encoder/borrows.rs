// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use rustc::ty::{self, TyCtxt, Ty, TypeVariants, TypeFlags};
use rustc::mir;
use rustc_data_structures::indexed_vec::Idx;
use utils::type_visitor::{self, TypeVisitor};

use prusti_interface::environment::{ProcedureImpl, Procedure};


#[derive(Debug)]
pub struct BorrowInfo {
    lifetime: String,
    blocking_paths: Vec<String>,    // Vec<rustc::mir::Lvalue>
    blocked_paths: Vec<String>,     // Vec<rustc::mir::Lvalue>
    //blocked_lifetimes: Vec<String>, TODO: Get this info from the constraints graph.
}

impl BorrowInfo {

    fn new(lifetime: String) -> BorrowInfo {
        BorrowInfo {
            lifetime: lifetime,
            blocking_paths: Vec::new(),
            blocked_paths: Vec::new(),
        }
    }

}

pub struct BorrowInfoCollectingVisitor<'a, 'tcx: 'a> {
    borrow_infos: Vec<BorrowInfo>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>,
    /// Can the currently analysed path block other paths? For return
    /// type this is initially true, and for parameters it is true below
    /// the first reference.
    is_path_blocking: bool,
    current_path: Vec<String>,
}

impl<'a, 'tcx> BorrowInfoCollectingVisitor<'a, 'tcx> {

    fn new(tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Self {
        BorrowInfoCollectingVisitor {
            borrow_infos: Vec::new(),
            tcx: tcx,
            is_path_blocking: false,
            current_path: Vec::new(),
        }
    }

    fn analyse_return_ty(&mut self, ty: Ty<'tcx>) {
        self.is_path_blocking = true;
        self.current_path = vec![String::from("_0")];
        self.visit_ty(ty);
        for borrow_info in self.borrow_infos.iter() {
            debug!("borrow_info: {:?}", borrow_info);
        }
    }

    fn extract_bound_region(&self, region: ty::Region<'tcx>) -> ty::BoundRegion {
        match region {
            &ty::RegionKind::ReFree(free_region) => free_region.bound_region,
            _ => unimplemented!(),
        }
    }

    fn get_or_create_borrow_info(&mut self, region: ty::BoundRegion) -> &mut BorrowInfo {
        let lifetime = match region {
            ty::BoundRegion::BrNamed(_, name) => {
                name.as_str().to_string()
            },
            _ => unimplemented!(),
        };
        if let Some(index) = self.borrow_infos.iter().position(|info| info.lifetime == lifetime) {
            &mut self.borrow_infos[index]
        } else {
            let borrow_info = BorrowInfo::new(lifetime);
            self.borrow_infos.push(borrow_info);
            self.borrow_infos.last_mut().unwrap()
        }
    }

}

impl<'a, 'tcx> TypeVisitor<'a, 'tcx> for BorrowInfoCollectingVisitor<'a, 'tcx> {

    fn tcx(&self) -> TyCtxt<'a, 'tcx, 'tcx> {
        self.tcx
    }

    fn visit_field(&mut self, field: &ty::FieldDef, substs: &'tcx ty::subst::Substs<'tcx>) {
        trace!("visit_field({:?})", field);
        self.current_path.push(field.name.as_str().to_string());
        type_visitor::walk_field(self, field, substs);
        self.current_path.pop();
    }

    fn visit_ref(&mut self, region: ty::Region<'tcx>, tym: ty::TypeAndMut<'tcx>) {
        trace!("visit_ref({:?}, {:?}) current_path={:?}", region, tym, self.current_path);
        self.current_path.push(String::from("*"));
        let bound_region = self.extract_bound_region(region);
        let is_path_blocking = self.is_path_blocking;
        let current_path = self.current_path.join(".");
        let borrow_info = self.get_or_create_borrow_info(bound_region);
        if is_path_blocking {
            borrow_info.blocking_paths.push(current_path);
        } else {
            borrow_info.blocked_paths.push(current_path);
        }
        type_visitor::walk_ref(self, region, tym);
        self.current_path.pop();
    }

}

pub fn compute_borrow_infos<'p, 'a, 'tcx>(
    procedure: &'p ProcedureImpl<'a, 'tcx>,
    tcx: TyCtxt<'a, 'tcx, 'tcx>) -> Vec<BorrowInfo>
    where
        'a: 'p,
        'tcx: 'a
{
    trace!("[compute_borrow_infos] enter name={}", procedure.get_name());
    let mir = procedure.get_mir();
    let return_ty = mir.return_ty();
    let mut visitor = BorrowInfoCollectingVisitor::new(tcx);
    visitor.analyse_return_ty(return_ty);
    //extract_top_references(return_ty, tcx);
    //let arg_count = mir.arg_count;
    //let mut args_ty = Vec::new();
    //for i in 1..arg_count+1 {
        //let local = mir::Local::new(i);
        //let arg_ty = mir.local_decls[local].ty;
        //args_ty.push(arg_ty);
        //trace!("arg ({}): {:?}", i, arg_ty);
    //}
    trace!("[compute_borrow_infos] exit");
    vec![]
}
