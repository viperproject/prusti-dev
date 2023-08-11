use vir_crate::polymorphic as vir;

use crate::encoder::{
    errors::{SpannedEncodingResult, WithSpan},
    mir::specifications::SpecificationsInterface,
    snapshot::interface::SnapshotEncoderInterface,
};
use prusti_interface::data::ProcedureDefId;
use prusti_rustc_interface::middle::ty::subst::SubstsRef;

use super::super::compute_key;

/// Encodes resource definitions and leak check definitions
/// Resource accesses are encoded in the pure code interpreter,
/// which calls PureFunctionEncoderInterface::encode_pure_function_use for them
pub(crate) trait ResourceEncoderInterface<'v, 'tcx> {
    fn ensure_resource_encoded(
        &self,
        identifier: &vir::FunctionIdentifier,
    ) -> SpannedEncodingResult<()>;

    fn encode_resource_def(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<()>;
}

impl<'v, 'tcx: 'tcx> ResourceEncoderInterface<'v, 'tcx>
    for crate::encoder::encoder::Encoder<'v, 'tcx>
{
    fn ensure_resource_encoded(
        &self,
        identifier: &vir::FunctionIdentifier,
    ) -> SpannedEncodingResult<()> {
        let function_descriptions = self
            .pure_function_encoder_state
            .function_descriptions
            .borrow();
        if let Some(function_description) = function_descriptions.get(identifier) {
            let function_description = function_description.clone();
            // We need to release the borrow here before encoding the function
            // because otherwise encoding recursive functions cause a panic.
            drop(function_descriptions);
            self.encode_resource_def(
                function_description.proc_def_id,
                function_description.parent_def_id,
                function_description.substs,
            )?;
        } else {
            unreachable!("a resource definition has been requested to be encoded, but no access to this resource has previously been encoded by the pure function encoder");
        }
        Ok(())
    }

    fn encode_resource_def(
        &self,
        proc_def_id: ProcedureDefId,
        parent_def_id: ProcedureDefId,
        substs: SubstsRef<'tcx>,
    ) -> SpannedEncodingResult<()> {
        assert!(
            self.is_resource(proc_def_id, Some(substs)),
            "procedure not marked as resource"
        );
        let key = compute_key(self, proc_def_id, parent_def_id, substs)?;
        if !self
            .pure_function_encoder_state
            .function_identifiers
            .borrow()
            .contains_key(&key)
            && !self
                .pure_function_encoder_state
                .pure_functions_encoding_started
                .borrow()
                .contains(&key)
        {
            self.pure_function_encoder_state
                .pure_functions_encoding_started
                .borrow_mut()
                .insert(key);

            let sig = self
                .env()
                .query
                .get_fn_sig_resolved(proc_def_id, substs, parent_def_id);
            let resource_name = self.encode_item_name(proc_def_id);
            let mut args = vec![vir::LocalVar::new("scope_id", vir::Type::Int)];
            let mut check_args = vec![];
            let mut concrete_args = vec![vir::Expr::Const(vir::ConstExpr {
                value: vir::Const::Int(-2),
                position: vir::Position::default(),
            })];
            for local_idx in 1..sig.skip_binder().inputs().len() {
                let local_ty = sig.input(local_idx);
                let local = prusti_rustc_interface::middle::mir::Local::from_usize(local_idx + 1);
                let var_name = format!("{local:?}_l_check"); // TODO: *ensure* that there are no local
                                                             // variable name clashes
                let var_span = self.get_spec_span(proc_def_id);
                let var_type = self
                    .encode_snapshot_type(local_ty.skip_binder())
                    .with_span(var_span)?;
                let local_var = vir::LocalVar::new(var_name, var_type);
                args.push(local_var.clone());
                check_args.push(local_var.clone());
                concrete_args.push(vir::Expr::local(local_var));
            }
            let resource = vir::Predicate::new_resource(resource_name.clone(), args.clone());

            let leak_check = if self.is_leak_checked(proc_def_id, Some(substs)) {
                let resource_access = vir::ResourceAccess {
                    name: resource_name,
                    args: concrete_args,
                    formal_arguments: args.clone(),
                    position: vir::Position::default(),
                };
                let check = vir::ForPerm {
                    variables: check_args,
                    access: resource_access,
                    body: Box::new(vir::Expr::Const(vir::ConstExpr {
                        value: vir::Const::Bool(false),
                        position: vir::Position::default(),
                    })),
                    position: vir::Position::default(),
                };
                Some(check)
            } else {
                None
            };
            self.insert_resource(resource, leak_check);
        }
        Ok(())
    }
}
