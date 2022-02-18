use super::borrows::{BorrowInfo, BorrowInfoCollectingVisitor};
use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    places, Encoder,
    mir::specifications::SpecificationsInterface
};
use log::trace;
use prusti_interface::environment::Environment;
use prusti_interface::specs::typed;
use rustc_hash::FxHashMap;
use rustc_hir::{
    def_id::{DefId, LocalDefId},
    Mutability,
};
use rustc_middle::{mir, ty, ty::FnSig, ty::subst::SubstsRef};
use std::{cell::RefCell, fmt};

pub(crate) trait ContractsEncoderInterface<'tcx> {
    /// Get a contract for a procedure's definition site, using MIR types for
    /// locals and places. Results are cached per DefId.
    fn get_mir_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>>;

    fn get_mir_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        call_substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>>;

    /// Get a contract for a procedure's definition site, using the
    /// `encoder::places` abstraction for locals and places. Results are cached
    /// per DefId.
    fn get_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>>;

    /// Get a contract for a call to a procedure, with particular argument and
    /// result substitutions.
    fn get_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        args: &[places::Local],
        target: places::Local,
        call_substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>>;
}

#[derive(Default)]
pub(crate) struct ContractsEncoderState<'tcx> {
    encoded_contracts: RefCell<FxHashMap<DefId, EncodingResult<ProcedureContractMirDef<'tcx>>>>,
}

/// Contract of a specific procedure. It is a separate struct from a
/// general procedure info because we want to be able to translate
/// procedure calls before translating call targets.
#[derive(Clone, Debug)]
pub struct ProcedureContractGeneric<L, P>
where
    L: fmt::Debug,
    P: fmt::Debug,
{
    /// Definition ID of the procedure to which the contract is attached.
    pub def_id: DefId,
    /// Formal arguments for which we should have permissions in the
    /// precondition. This includes both borrows and moved in values.
    /// For example, if `_2` is in the vector, this means that we have
    /// `T(_2)` in the precondition.
    pub args: Vec<L>,
    /// Borrowed arguments that are directly returned to the caller (not via
    /// a magic wand). For example, if `*(_2.1).0` is in the vector, this
    /// means that we have `T(old[precondition](_2.1.ref.0))` in the
    /// postcondition. It also includes information about the mutability
    /// of the original reference.
    pub returned_refs: Vec<(P, Mutability)>,
    /// The returned value for which we should have permission in
    /// the postcondition.
    pub returned_value: L,
    /// Magic wands passed out of the procedure.
    /// TODO: Implement support for `blocked_lifetimes` via nested magic wands.
    pub borrow_infos: Vec<BorrowInfo<P>>,
    /// The functional specification: precondition and postcondition
    pub specification: typed::ProcedureSpecification,
}

impl<L: fmt::Debug, P: fmt::Debug> ProcedureContractGeneric<L, P> {
    pub fn functional_precondition<'a, 'tcx>(
        &'a self,
        env: &'a Environment<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> Vec<(LocalDefId, SubstsRef<'tcx>)> {
        match &self.specification.pres {
            typed::SpecificationItem::Empty => vec![],
            typed::SpecificationItem::Inherent(pres)
            | typed::SpecificationItem::Refined(_, pres) => pres.iter()
                .map(|inherent_def_id| (
                    *inherent_def_id,
                    substs,
                ))
                .collect(),
            typed::SpecificationItem::Inherited(pres) => pres.iter()
                .map(|inherited_def_id| (
                    *inherited_def_id,
                    // This uses the substs of the current method and
                    // resolves them to the substs of the trait; however,
                    // we are actually resolving to a specification item.
                    // This works because the generics of the specification
                    // items are the same as the generics of the method on
                    // which they are declared.
                    env.find_trait_method_substs(self.def_id, substs).unwrap().1,
                ))
                .collect(),
        }
    }

    pub fn functional_postcondition<'a, 'tcx>(
        &'a self,
        env: &'a Environment<'tcx>,
        substs: SubstsRef<'tcx>,
    ) -> Vec<(LocalDefId, SubstsRef<'tcx>)> {
        match &self.specification.posts {
            typed::SpecificationItem::Empty => vec![],
            typed::SpecificationItem::Inherent(posts)
            | typed::SpecificationItem::Refined(_, posts) => posts.iter()
                .map(|inherent_def_id| (
                    *inherent_def_id,
                    substs,
                ))
                .collect(),
            typed::SpecificationItem::Inherited(posts) => posts.iter()
                .map(|inherited_def_id| (
                    *inherited_def_id,
                    // Same comment as `functional_precondition` applies.
                    env.find_trait_method_substs(self.def_id, substs).unwrap().1,
                ))
                .collect(),
        }
    }

    pub fn pledges(&self) -> impl Iterator<Item = &typed::Pledge> + '_ {
        self.specification.pledges.extract_with_selective_replacement_iter()
    }
}

/// Procedure contract as it is defined in MIR.
pub type ProcedureContractMirDef<'tcx> = ProcedureContractGeneric<mir::Local, mir::Place<'tcx>>;

/// Specialized procedure contract for use in translation.
pub type ProcedureContract<'tcx> = ProcedureContractGeneric<places::Local, places::Place<'tcx>>;

impl<L: fmt::Debug, P: fmt::Debug> fmt::Display for ProcedureContractGeneric<L, P> {
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

fn get_place_root(place: &mir::Place) -> mir::Local {
    // match place {
    //     &mir::Place::Local(local) => local,
    //     &mir::Place::Projection(ref projection) => get_place_root(&projection.base),
    //     _ => unimplemented!(),
    // }
    place.local
}

impl<'tcx> ProcedureContractMirDef<'tcx> {
    /// Specialize to the definition site contract.
    pub fn to_def_site_contract(&self) -> ProcedureContract<'tcx> {
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info
                    .blocking_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
                blocked_paths: info
                    .blocked_paths
                    .iter()
                    .map(|(p, m)| (p.into(), *m))
                    .collect(),
            })
            .collect();
        ProcedureContract {
            def_id: self.def_id,
            args: self.args.iter().map(|&a| a.into()).collect(),
            returned_refs: self
                .returned_refs
                .iter()
                .map(|(r, m)| (r.into(), *m))
                .collect(),
            returned_value: self.returned_value.into(),
            borrow_infos,
            specification: self.specification.clone(),
        }
    }

    /// Specialize to the call site contract.
    pub fn to_call_site_contract(
        &self,
        args: &[places::Local],
        target: places::Local,
    ) -> ProcedureContract<'tcx> {
        assert_eq!(self.args.len(), args.len());
        let mut substitutions = FxHashMap::default();
        substitutions.insert(self.returned_value, target);
        for (from, to) in self.args.iter().zip(args) {
            substitutions.insert(*from, *to);
        }
        let substitute = |(place, mutability): &(_, Mutability)| {
            let root = &get_place_root(place);
            let substitute_place = places::Place::SubstitutedPlace {
                substituted_root: *substitutions.get(root).unwrap(),
                place: *place,
            };
            (substitute_place, *mutability)
        };
        let borrow_infos = self
            .borrow_infos
            .iter()
            .map(|info| BorrowInfo {
                region: info.region,
                blocking_paths: info.blocking_paths.iter().map(&substitute).collect(),
                blocked_paths: info.blocked_paths.iter().map(&substitute).collect(),
            })
            .collect();
        let returned_refs = self.returned_refs.iter().map(&substitute).collect();
        ProcedureContract {
            def_id: self.def_id,
            args: args.to_vec(),
            returned_refs,
            returned_value: target,
            borrow_infos,
            specification: self.specification.clone(),
        }
    }
}

impl<'v, 'tcx: 'v> ContractsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_mir_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
        self.contracts_encoder_state
            .encoded_contracts
            .borrow_mut()
            .entry(proc_def_id)
            .or_insert_with(|| get_procedure_contract(self, proc_def_id, substs))
            .clone()
    }

    fn get_mir_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        call_substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
        let (called_def_id, call_substs) = self.env()
            .resolve_method_call(caller_def_id, called_def_id, call_substs);
        // let spec = self.get_procedure_specs(called_def_id, call_substs)
        //     .unwrap_or_else(typed::ProcedureSpecification::empty);
        let contract = get_procedure_contract(
            self,
            called_def_id,
            call_substs,
        )?;
        Ok(contract)
    }

    fn get_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        self.get_mir_procedure_contract_for_def(proc_def_id, substs)
            .as_ref()
            .map(|contract| contract.to_def_site_contract())
            .map_err(|err| err.clone())
    }

    fn get_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        args: &[places::Local],
        target: places::Local,
        call_substs: SubstsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        let (called_def_id, call_substs) = self.env()
            .resolve_method_call(caller_def_id, called_def_id, call_substs);
        let contract = get_procedure_contract(
            self,
            called_def_id,
            call_substs
        )?;
        Ok(contract.to_call_site_contract(args, target))
    }
}

fn get_procedure_contract<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    use crate::rustc_middle::ty::subst::Subst;

    let env = encoder.env();
    let tcx = env.tcx();
    let specification = encoder
        .get_procedure_specs(proc_def_id, substs)
        .unwrap_or_else(typed::ProcedureSpecification::empty);

    trace!("[get_procedure_contract] enter name={:?}", proc_def_id);

    let args_ty: Vec<(mir::Local, ty::Ty<'tcx>)>;
    let return_ty;

    if !tcx.is_closure(proc_def_id) {
        // FIXME: "skip_binder" is most likely wrong
        // FIXME: Replace with FakeMirEncoder.
        let fn_sig: FnSig = env.tcx().fn_sig(proc_def_id).skip_binder()
            .subst(env.tcx(), substs);
        if fn_sig.c_variadic {
            return Err(EncodingError::unsupported(
                "variadic functions are not supported",
            ));
        }
        args_ty = (0usize..fn_sig.inputs().len())
            .map(|i| (mir::Local::from_usize(i + 1), fn_sig.inputs()[i]))
            .collect();
        return_ty = fn_sig.output();
    } else {
        let mir = env.local_mir(proc_def_id.expect_local(), substs);
        // local_decls:
        // _0    - return, with closure's return type
        // _1    - closure's self
        // _2... - actual arguments
        // arg_count includes the extra self _1
        args_ty = (1usize..=mir.arg_count)
            .map(|i| {
                (
                    mir::Local::from_usize(i),
                    mir.local_decls[mir::Local::from_usize(i)].ty,
                )
            })
            .collect();
        return_ty = mir.local_decls[mir::Local::from_usize(0)].ty;
    }

    let mut fake_mir_args = Vec::new();
    let mut fake_mir_args_ty = Vec::new();
    for (local, arg_ty) in args_ty {
        fake_mir_args.push(local);
        fake_mir_args_ty.push(arg_ty);
    }

    let mut visitor = BorrowInfoCollectingVisitor::new(tcx);
    for (arg, arg_ty) in fake_mir_args.iter().zip(fake_mir_args_ty) {
        visitor.analyse_arg(*arg, arg_ty)?;
    }
    visitor.analyse_return_ty(return_ty)?;
    let borrow_infos: Vec<_> = visitor
        .borrow_infos
        .into_iter()
        .filter(|info|
            !info.blocked_paths.is_empty()
            && !info.blocking_paths.is_empty()
            && info.blocked_paths.iter().any(|(_, mutability)| matches!(mutability, Mutability::Mut))
        ).collect();
    let is_not_blocked = |place: &mir::Place<'tcx>| {
        !borrow_infos.iter().any(|info| {
            info.blocked_paths
                .iter()
                .any(|(blocked_place, _)| blocked_place == place)
        })
    };

    let returned_refs: Vec<_> = visitor
        .references_in
        .into_iter()
        .filter(|(place, _)| is_not_blocked(place))
        .collect();
    let contract = ProcedureContractGeneric {
        def_id: proc_def_id,
        args: fake_mir_args,
        returned_refs,
        returned_value: mir::RETURN_PLACE,
        borrow_infos,
        specification,
    };

    trace!("[get_procedure_contract] exit result={}", contract);
    Ok(contract)
}
