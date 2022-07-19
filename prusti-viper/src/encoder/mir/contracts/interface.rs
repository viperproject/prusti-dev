use super::{
    borrows::BorrowInfoCollectingVisitor,
    contracts::{ProcedureContract, ProcedureContractGeneric, ProcedureContractMirDef},
};
use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    mir::specifications::SpecificationsInterface,
    places, Encoder,
};
use log::trace;
use prusti_interface::specs::typed;
use prusti_rustc_interface::{
    hir::{def_id::DefId, Mutability},
    middle::{
        mir, ty,
        ty::{subst::SubstsRef, FnSig},
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
        let (called_def_id, call_substs) =
            self.env()
                .resolve_method_call(caller_def_id, called_def_id, call_substs);
        // let spec = self.get_procedure_specs(called_def_id, call_substs)
        //     .unwrap_or_else(typed::ProcedureSpecification::empty);
        let contract = get_procedure_contract(self, called_def_id, call_substs)?;
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
        let (called_def_id, call_substs) =
            self.env()
                .resolve_method_call(caller_def_id, called_def_id, call_substs);
        let contract = get_procedure_contract(self, called_def_id, call_substs)?;
        Ok(contract.to_call_site_contract(args, target))
    }
}

fn get_procedure_contract<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    proc_def_id: DefId,
    substs: SubstsRef<'tcx>,
) -> EncodingResult<ProcedureContractMirDef<'tcx>> {
    use prusti_rustc_interface::middle::ty::subst::Subst;

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
        let fn_sig: FnSig =
            ty::EarlyBinder(env.tcx().fn_sig(proc_def_id).skip_binder()).subst(env.tcx(), substs);
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
