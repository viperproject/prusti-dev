use crate::encoder::{Encoder, borrows::ProcedureContract};
use crate::encoder::errors::{EncodingError, ErrorCtxt};
use crate::encoder::borrows::compute_procedure_contract;
use crate::encoder::mir_encoder::{MirEncoder, PlaceEncoder};
use crate::encoder::snapshot_spec_patcher::SnapshotSpecPatcher;
use prusti_interface::{
    environment::{
        Procedure,
        Environment
    },
    data::ProcedureDefId,
    specs::typed,
};
use prusti_common::vir;
use prusti_common::vir::ExprIterator;
use rustc_middle::{ty, mir};
use log::{debug, trace};
use rustc_hir as hir;

pub enum SpecFunctionKind {
    Pre,
    Post,
    HistInv
}

pub struct SpecFunctionEncoder<'p, 'v: 'p, 'tcx: 'v> {
    env: &'v Environment<'tcx>,
    encoder: &'p Encoder<'v, 'tcx>,
    procedure: &'p Procedure<'p, 'tcx>,
    proc_def_id: ProcedureDefId,
    contract: Option<typed::SpecificationSet<'tcx>>,
    mir: &'p mir::Body<'tcx>,
    mir_encoder: MirEncoder<'p, 'v, 'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> SpecFunctionEncoder<'p, 'v, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'tcx>,
               procedure: &'p Procedure<'p, 'tcx>) -> Self {
        Self {
            env: encoder.env(),
            encoder: encoder,
            procedure: procedure,
            proc_def_id: procedure.get_id(),
            contract: encoder.get_spec_by_def_id(procedure.get_id()),
            mir: procedure.get_mir(),
            mir_encoder: MirEncoder::new(encoder, procedure.get_mir(), procedure.get_id())
        }
    }

    pub fn encode(&self) -> Result<Vec<vir::Function>, EncodingError> {
        let pre_name = self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                          SpecFunctionKind::Pre);
        let post_name = self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                           SpecFunctionKind::Post);

        if let None = self.contract {
            return Ok(Vec::new());
        }

        let contract = compute_procedure_contract(
            self.proc_def_id,
            self.encoder.env().tcx(),
            self.contract.clone().unwrap(),
            Some(&self.encoder.current_tymap())
        ).to_def_site_contract();

        let pre_func = self.encode_pre_spec_func(&contract);

        Ok(vec! [pre_func])
    }

    fn encode_pre_spec_func(&self, contract: &ProcedureContract<'tcx>) -> vir::Function {
        let mut func_spec: Vec<vir::Expr> = vec![];

        let encoded_args: Vec<vir::LocalVar> = contract
            .args
            .iter()
            .map(|local| self.encode_local(local.clone().into()).into())
            .collect();

        for item in contract.functional_precondition() {
            func_spec.push(self.encoder.encode_assertion(
                &item,
                &self.mir,
                &"",
                &encoded_args.iter().map(|e| -> vir::Expr { e.into() }).collect::<Vec<_>>(),
                None,
                true,
                None,
                ErrorCtxt::GenericExpression,
            ));
        }

        vir::Function {
            name: self.encoder.encode_spec_func_name(self.procedure.get_id(),
                                                     SpecFunctionKind::Pre),
            formal_args: encoded_args,
            return_type: vir::Type::Bool,
            pres: Vec::new(),
            posts: Vec::new(),
            body: Some(func_spec.into_iter()
                                .map(|post| SnapshotSpecPatcher::new(self.encoder).patch_spec(post))
                                .conjoin()),
        }
    }

    fn encode_local(&self, local: mir::Local) -> vir::LocalVar {
        let var_name = self.mir_encoder.encode_local_var_name(local);
        let var_type = self
            .encoder
            .encode_value_or_ref_type(self.mir_encoder.get_local_ty(local));
        vir::LocalVar::new(var_name, var_type)
    }
}
