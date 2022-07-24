use crate::encoder::snapshot::interface::SnapshotEncoderInterface;
use crate::encoder::Encoder;
use crate::encoder::errors::{ErrorCtxt, SpannedEncodingResult, WithSpan};
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use crate::encoder::mir::{
    contracts::{
        ContractsEncoderInterface,
        ProcedureContract,
    },
    pure::SpecificationEncoderInterface,
    specifications::SpecificationsInterface,
};
use prusti_interface::{
    environment::{
        Procedure
    },
    data::ProcedureDefId,
};
use vir_crate::polymorphic as vir;
use vir_crate::polymorphic::ExprIterator;
use prusti_rustc_interface::middle::{mir, ty::subst::SubstsRef};
use prusti_rustc_interface::span::Span;

pub enum SpecFunctionKind {
    Pre,
    Post,
    HistInv
}

pub struct SpecFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    encoder: &'p Encoder<'v, 'tcx>,
    procedure: &'p Procedure<'tcx>,
    span: Span,
    proc_def_id: ProcedureDefId,
    is_closure: bool,
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
    // TODO(tymap): which substs are these?
    substs: SubstsRef<'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>,
               procedure: &'p Procedure<'tcx>,
               substs: SubstsRef<'tcx>) -> Self {
        Self {
            encoder,
            procedure,
            span: procedure.get_span(),
            proc_def_id: procedure.get_id(),
            is_closure: encoder.env().tcx().is_closure(procedure.get_id()),
            mir_encoder: MirEncoder::new(encoder, procedure.get_mir(), procedure.get_id()),
            substs,
        }
    }

    pub fn encode(&self) -> SpannedEncodingResult<Vec<vir::Function>> {
        let _pre_name = self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                          SpecFunctionKind::Pre);
        let _post_name = self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                           SpecFunctionKind::Post);

        if self.encoder.get_procedure_specs(self.proc_def_id, self.substs).is_none() {
            return Ok(vec![]);
        }

        let contract = self.encoder.get_procedure_contract_for_def(self.proc_def_id, self.substs)
            .with_span(self.span)?;

        let pre_func = self.encode_pre_spec_func(&contract)?;
        let post_func = self.encode_post_spec_func(&contract)?;

        Ok(vec![pre_func, post_func])
    }

    fn encode_pre_spec_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()))
            .collect::<Result<Vec<_>, _>>()?;

        for (assertion, assertion_substs) in contract.functional_precondition(self.encoder.env(), self.substs) {
            let encoded_assertion = self.encoder.encode_assertion(
                &assertion,
                None,
                &encoded_args
                    .iter()
                    .map(|e| -> vir::Expr { e.into() }).collect::<Vec<_>>(),
                None,
                true,
                self.proc_def_id,
                assertion_substs,
            )?;
            self.encoder.error_manager().set_error(
                encoded_assertion.pos(),
                ErrorCtxt::PureFunctionDefinition,
            );
            func_spec.push(encoded_assertion);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                     SpecFunctionKind::Pre),
            type_arguments: Vec::new(), // FIXME: This is probably wrong.
            formal_args: encoded_args.into_iter()
                                     .skip(if self.is_closure { 1 } else { 0 }) // FIXME: "self" is skipped, see TypeEncoder
                                     .collect(),
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(self.encoder.patch_snapshots(func_spec.into_iter().conjoin()).with_span(self.span)?),
        })
    }

    fn encode_post_spec_func(&self, contract: &ProcedureContract<'tcx>)
        -> SpannedEncodingResult<vir::Function> {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local((*local).into()))
            .collect::<Result<Vec<_>, _>>()?;
        let encoded_return = self.encode_local(contract.returned_value.into())?;
        // encoded_args:
        // _1    - closure "self"
        // _2... - additional arguments
        // encoded return: _0

        for (assertion, assertion_substs) in contract.functional_postcondition(self.encoder.env(), self.substs) {
            let encoded_assertion = self.encoder.encode_assertion(
                &assertion,
                None,
                &encoded_args
                    .iter()
                    .map(|e| -> vir::Expr { e.into() }).collect::<Vec<_>>(),
                Some(&encoded_return.clone().into()),
                true,
                self.proc_def_id,
                assertion_substs,
            )?;
            self.encoder.error_manager().set_error(
                encoded_assertion.pos(),
                ErrorCtxt::PureFunctionDefinition,
            );
            func_spec.push(encoded_assertion);
        }

        Ok(vir::Function {
            name: self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                     SpecFunctionKind::Post),
            type_arguments: Vec::new(), // FIXME: This is probably wrong.
            formal_args: encoded_args.into_iter()
                                     .skip(if self.is_closure { 1 } else { 0 }) // FIXME: "self" is skipped, see TypeEncoder
                                     .chain(std::iter::once(encoded_return))
                                     .collect(),
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(self.encoder.patch_snapshots(func_spec.into_iter().conjoin()).with_span(self.span)?),
        })
    }

    fn encode_local(&self, local: mir::Local) -> SpannedEncodingResult<vir::LocalVar> {
        let var_name = self.mir_encoder.encode_local_var_name(local);
        let var_type = self
            .encoder
            .encode_snapshot_type(self.mir_encoder.get_local_ty(local))
            .with_span(self.span)?;
        Ok(vir::LocalVar::new(var_name, var_type))
    }
}
