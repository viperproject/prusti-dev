use super::{
    borrows::BorrowInfoCollectingVisitor,
    contracts::{ProcedureContract, ProcedureContractGeneric, ProcedureContractMirDef},
};
use crate::{
    encoder::{
        errors::EncodingResult, mir::specifications::SpecificationsInterface, places, Encoder,
    },
    error_unsupported,
};
use log::trace;
use prusti_interface::specs::typed;
use prusti_rustc_interface::{
    hir::{def_id::DefId, Mutability},
    middle::{
        mir, ty,
        ty::{FnSig, GenericArgsRef},
    },
};
use rustc_hash::FxHashMap;
use std::cell::RefCell;

pub(crate) trait ContractsEncoderInterface<'tcx> {
    /// Get a contract for a procedure's definition site, using MIR types for
    /// locals and places. Results are cached per DefId.
    fn get_mir_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>>;

    fn get_mir_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        call_substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>>;

    /// Get a contract for a procedure's definition site, using the
    /// `encoder::places` abstraction for locals and places. Results are cached
    /// per DefId.
    fn get_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>>;

    /// Get a contract for a call to a procedure, with particular argument and
    /// result substitutions.
    fn get_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        args: &[places::Local],
        target: places::Local,
        call_substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>>;
}

#[derive(Default)]
pub(crate) struct ContractsEncoderState<'tcx> {
    encoded_contracts: RefCell<FxHashMap<DefId, EncodingResult<ProcedureContractMirDef<'tcx>>>>,
}

impl<'v, 'tcx: 'v> ContractsEncoderInterface<'tcx> for super::super::super::Encoder<'v, 'tcx> {
    fn get_mir_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
        self.contracts_encoder_state
            .encoded_contracts
            .borrow_mut()
            .entry(proc_def_id)
            .or_insert_with(|| {
                let specification = self
                    .get_procedure_specs(proc_def_id, substs)
                    .unwrap_or_else(|| typed::ProcedureSpecification::empty(proc_def_id));
                get_procedure_contract(self, specification, proc_def_id, substs)
            })
            .clone()
    }

    fn get_mir_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        call_substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
        let (called_def_id, call_substs) =
            self.env()
                .query
                .resolve_method_call(caller_def_id, called_def_id, call_substs);
        let specification = self
            .get_procedure_specs_for_call(called_def_id, caller_def_id, call_substs)
            .unwrap_or_else(|| typed::ProcedureSpecification::empty(called_def_id));
        let contract = get_procedure_contract(self, specification, called_def_id, call_substs)?;
        Ok(contract)
    }

    #[tracing::instrument(level = "debug", skip(self))]
    fn get_procedure_contract_for_def(
        &self,
        proc_def_id: DefId,
        substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        self.get_mir_procedure_contract_for_def(proc_def_id, substs)
            .as_ref()
            .map(|contract| contract.to_def_site_contract())
            .map_err(|err| err.clone())
    }

    #[tracing::instrument(level = "debug", skip(self))]
    fn get_procedure_contract_for_call(
        &self,
        caller_def_id: DefId,
        called_def_id: DefId,
        args: &[places::Local],
        target: places::Local,
        call_substs: GenericArgsRef<'tcx>,
    ) -> EncodingResult<ProcedureContract<'tcx>> {
        let (called_def_id, call_substs) =
            self.env()
                .query
                .resolve_method_call(caller_def_id, called_def_id, call_substs);
        let specification = self
            .get_procedure_specs_for_call(called_def_id, caller_def_id, call_substs)
            .unwrap_or_else(|| typed::ProcedureSpecification::empty(called_def_id));
        let contract = get_procedure_contract(self, specification, called_def_id, call_substs)?;
        Ok(contract.to_call_site_contract(args, target))
    }
}

#[tracing::instrument(level = "debug", skip(encoder, specification))]
fn get_procedure_contract<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    specification: typed::ProcedureSpecification,
    proc_def_id: DefId,
    substs: GenericArgsRef<'tcx>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    let env = encoder.env();
    let args_ty: Vec<(mir::Local, ty::Ty<'tcx>)>;
    let return_ty;

    if !env.query.is_closure(proc_def_id) {
        // FIXME: "skip_binder" is most likely wrong
        // FIXME: Replace with FakeMirEncoder.
        let fn_sig: FnSig = env.query.get_fn_sig(proc_def_id, substs).skip_binder();
        if fn_sig.c_variadic {
            error_unsupported!("variadic functions are not supported");
        }
        args_ty = (0usize..fn_sig.inputs().len())
            .map(|i| (mir::Local::from_usize(i + 1), fn_sig.inputs()[i]))
            .collect();
        return_ty = fn_sig.output();
    } else {
        let mir = env
            .body
            .get_impure_fn_body(proc_def_id.expect_local(), substs);
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

    let mut visitor = BorrowInfoCollectingVisitor::new(env.tcx());
    for (arg, arg_ty) in fake_mir_args.iter().zip(fake_mir_args_ty) {
        visitor.analyse_arg(*arg, arg_ty)?;
    }
    visitor.analyse_return_ty(return_ty)?;
    let borrow_infos: Vec<_> = visitor
        .borrow_infos
        .into_iter()
        .filter(|info| {
            !info.blocked_paths.is_empty()
                && !info.blocking_paths.is_empty()
                && info
                    .blocked_paths
                    .iter()
                    .any(|(_, mutability)| matches!(mutability, Mutability::Mut))
        })
        .collect();
    let is_not_blocked = |place: mir::Place<'tcx>| {
        !borrow_infos.iter().any(|info| {
            info.blocked_paths
                .iter()
                .any(|(blocked_place, _)| *blocked_place == place)
        })
    };

    let returned_refs: Vec<_> = visitor
        .references_in
        .into_iter()
        .filter(|(place, _)| is_not_blocked(*place))
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
