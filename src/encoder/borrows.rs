// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::fmt;
use rustc::ty::{self, TyCtxt, Ty};
use rustc::hir;
use rustc::mir;
use rustc_data_structures::indexed_vec::Idx;
use utils::type_visitor::{self, TypeVisitor};
use encoder::places;
use std::collections::HashMap;

use prusti_interface::data::ProcedureDefId;


#[derive(Clone, Debug)]
pub struct BorrowInfo<P>
    where
        P: fmt::Debug
{
    /// Region of this borrow.
    pub region: ty::BoundRegion,
    pub blocking_paths: Vec<P>,
    pub blocked_paths: Vec<P>,
    //blocked_lifetimes: Vec<String>, TODO: Get this info from the constraints graph.
}

impl<P: fmt::Debug> BorrowInfo<P> {

    fn new(region: ty::BoundRegion) -> Self {
        BorrowInfo {
            region: region,
            blocking_paths: Vec::new(),
            blocked_paths: Vec::new(),
        }
    }

}

impl<P: fmt::Debug> fmt::Display for BorrowInfo<P> {

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let lifetime = match self.region {
            ty::BoundRegion::BrAnon(id) => format!("#{}", id),
            ty::BoundRegion::BrNamed(_, name) => name.to_string(),
            _ => unimplemented!(),
        };
        writeln!(f, "BorrowInfo<{}> {{", lifetime)?;
        for path in self.blocking_paths.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "  --*")?;
        for path in self.blocked_paths.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "}}")
    }

}

/// Contract of a specific procedure. It is a separate struct from a
/// general procedure info because we want to be able to translate
/// procedure calls before translating call targets.
/// TODO: Move to some properly named module.
#[derive(Clone)]
pub struct ProcedureContractGeneric<L, P>
    where
        L: fmt::Debug,
        P: fmt::Debug
{
    /// Formal arguments for which we should have permissions in the
    /// precondition. This includes both borrows and moved in values.
    /// For example, if `_2` is in the vector, this means that we have
    /// `T(_2)` in the precondition.
    pub args: Vec<L>,
    /// Borrowed arguments that are directly returned to the caller (not via
    /// a magic wand). For example, if `*(_2.1).0` is in the vector, this
    /// means that we have `T(old[precondition](_2.1.ref.0))` in the
    /// postcondition.
    pub returned_refs: Vec<P>,
    /// The returned value for which we should have permission in
    /// the postcondition.
    pub returned_value: L,
    /// Magic wands passed out of the procedure.
    /// TODO: Implement support for `blocked_lifetimes` via nested magic wands.
    pub borrow_infos: Vec<BorrowInfo<P>>,
}

/// Procedure contract as it is defined in MIR.
pub type ProcedureContractMirDef<'tcx> = ProcedureContractGeneric<mir::Local, mir::Place<'tcx>>;

/// Specialized procedure contract for use in translation.
pub type ProcedureContract<'tcx> = ProcedureContractGeneric<places::Local, places::Place<'tcx>>;

impl<L: fmt::Debug, P: fmt::Debug> fmt::Display for ProcedureContractGeneric<L, P>
{

    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        writeln!(f, "ProcedureContract {{")?;
        writeln!(f, "IN:")?;
        for path in self.args.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "OUT:")?;
        for path in self.returned_refs.iter() {
            writeln!(f, "  {:?}", path)?;
        }
        writeln!(f, "MAGIC:")?;
        for borrow_info in self.borrow_infos.iter() {
            writeln!(f, "{}", borrow_info)?;
        }
        writeln!(f, "}}")
    }

}

fn get_place_root<'tcx>(place: &mir::Place<'tcx>) -> mir::Local {
    match place {
        &mir::Place::Local(local) => local,
        &mir::Place::Projection(ref projection) => get_place_root(&projection.base),
        _ => unimplemented!(),
    }
}

impl<'tcx> ProcedureContractMirDef<'tcx> {

    /// Specialize to the definition site contract.
    pub fn to_def_site_contract(&self) -> ProcedureContract<'tcx> {
        let borrow_infos = self.borrow_infos
            .iter()
            .map(|info| {
                BorrowInfo {
                    region: info.region,
                    blocking_paths: info.blocking_paths.iter().map(|p| p.into()).collect(),
                    blocked_paths: info.blocked_paths.iter().map(|p| p.into()).collect(),
                }
            })
            .collect();
        ProcedureContract {
            args: self.args.iter().map(|&a| a.into()).collect(),
            returned_refs: self.returned_refs.iter().map(|r| r.into()).collect(),
            returned_value: self.returned_value.into(),
            borrow_infos: borrow_infos,
        }
    }

    /// Specialize to the call site contract.
    pub fn to_call_site_contract(&self, args: &Vec<places::Local>, target: places::Local
                                 ) -> ProcedureContract<'tcx> {
        assert!(self.args.len() == args.len());
        let mut substitutions = HashMap::new();
        substitutions.insert(self.returned_value, target);
        for (from, to) in self.args.iter().zip(args) {
            substitutions.insert(*from, *to);
        }
        let substitute = |place| {
            let root = &get_place_root(place);
            places::Place::SubstitutedPlace {
                substituted_root: *substitutions.get(root).unwrap(),
                place: place.clone(),
            }
        };
        let borrow_infos = self.borrow_infos
            .iter()
            .map(|info| {
                BorrowInfo {
                    region: info.region,
                    blocking_paths: info.blocking_paths.iter().map(&substitute).collect(),
                    blocked_paths: info.blocked_paths.iter().map(&substitute).collect(),
                }
            })
            .collect();
        ProcedureContract {
            args: args.clone(),
            returned_refs: self.returned_refs.iter().map(&substitute).collect(),
            returned_value: target,
            borrow_infos: borrow_infos,
        }
    }

}

pub struct BorrowInfoCollectingVisitor<'a, 'tcx: 'a> {
    borrow_infos: Vec<BorrowInfo<mir::Place<'tcx>>>,
    /// References that were passed as arguments. We are interested only in
    /// references that can be blocked.
    references_in: Vec<mir::Place<'tcx>>,
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
            references_in: Vec::new(),
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

    fn get_or_create_borrow_info(&mut self,
                                 region: ty::BoundRegion) -> &mut BorrowInfo<mir::Place<'tcx>> {
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

    fn visit_ref(&mut self, region: ty::Region<'tcx>, ty: ty::Ty<'tcx>, mutability: hir::Mutability) {
        trace!("visit_ref({:?}, {:?}, {:?}) current_path={:?}", region, ty, mutability, self.current_path);
        let bound_region = self.extract_bound_region(region);
        let is_path_blocking = self.is_path_blocking;
        let old_path = self.current_path.take().unwrap();
        let current_path = old_path.clone().deref();
        self.current_path = Some(current_path.clone());
        let borrow_info = self.get_or_create_borrow_info(bound_region);
        if is_path_blocking {
            borrow_info.blocking_paths.push(current_path);
        } else {
            borrow_info.blocked_paths.push(current_path.clone());
            self.references_in.push(current_path);
        }
        self.is_path_blocking = true;
        //type_visitor::walk_ref(self, region, ty, mutability);
        self.is_path_blocking = is_path_blocking;
        self.current_path = Some(old_path);
    }

    fn visit_raw_ptr(&mut self, ty: ty::Ty<'tcx>, mutability: hir::Mutability) {
        trace!("visit_raw_ptr({:?}, {:?}) current_path={:?}", ty, mutability, self.current_path);
        // TODO
        warn!("BorrowInfoCollectingVisitor::visit_raw_ptr is unimplemented");
    }
}

pub fn compute_procedure_contract<'p, 'a, 'tcx>(
    proc_def_id: ProcedureDefId,
    tcx: TyCtxt<'a, 'tcx, 'tcx>) -> ProcedureContractMirDef<'tcx>
    where
        'a: 'p,
        'tcx: 'a
{
    trace!("[compute_borrow_infos] enter name={:?}", proc_def_id);
    // TODO: this function should use HIR instead of MIR
    if let None = tcx.hir.as_local_node_id(proc_def_id) {
        unimplemented!("We don't support non-local procedure calls (yet)")
    }
    let mir = tcx.mir_validated(proc_def_id).borrow();
    let return_ty = mir.return_ty();
    let mut visitor = BorrowInfoCollectingVisitor::new(tcx);
    let mut args = Vec::new();
    for arg in mir.args_iter() {
        args.push(arg);
        let arg_decl = &mir.local_decls[arg];
        visitor.analyse_arg(arg, arg_decl.ty);
    }
    visitor.analyse_return_ty(return_ty);
    let borrow_infos: Vec<_> = visitor
        .borrow_infos
        .into_iter()
        .filter(|info|
                !info.blocked_paths.is_empty() &&
                !info.blocking_paths.is_empty())
        .collect();
    let is_not_blocked = |place: &mir::Place<'tcx>| {
        !borrow_infos
            .iter()
            .any(|info| info.blocked_paths.contains(place))
    };
    let returned_refs: Vec<_> = visitor
        .references_in
        .into_iter()
        .filter(is_not_blocked)
        .collect();
    let contract = ProcedureContractGeneric {
        args: args,
        returned_refs: returned_refs,
        returned_value: mir::RETURN_PLACE,
        borrow_infos: borrow_infos,
    };
    trace!("[compute_borrow_infos] exit result={}", contract);
    contract
}
