use super::super::PredicateKind;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        builtin_methods::CallContext,
        footprint::FootprintInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        snapshots::{IntoSnapshotLowerer, SnapshotValuesInterface},
    },
};
use rustc_hash::FxHashMap;
use vir_crate::{
    common::{identifier::WithIdentifier, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super::super::super) struct FramedExpressionToSnapshot<'a> {
    framing_variables: &'a [vir_mid::VariableDecl],
}

impl<'a> FramedExpressionToSnapshot<'a> {
    pub(in super::super::super::super::super) fn for_function_body(
        framing_variables: &'a [vir_mid::VariableDecl],
    ) -> Self {
        Self { framing_variables }
    }

    /// Find a base of type struct that has an invariant.
    fn obtain_invariant<'e>(
        &mut self,
        lowerer: &mut Lowerer,
        expression: &'e vir_mid::Expression,
    ) -> SpannedEncodingResult<(
        &'e vir_mid::Expression,
        vir_mid::Expression,
        Vec<vir_mid::Expression>,
    )> {
        let ty = expression.get_type();
        if ty.is_struct() {
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct {
                structural_invariant: Some(invariant),
                ..
            }) = type_decl
            {
                let self_place = vir_mid::VariableDecl::self_variable(ty.clone());
                return Ok((expression, self_place.into(), invariant));
            } else {
                unimplemented!("TODO: A proper error message that only permissions from non-nested structs are supported.");
            }
        } else {
            let (base_place, parent, invariant) = self.obtain_invariant(
                lowerer,
                expression
                    .get_parent_ref()
                    .expect("TODO: A proper error message that the permission has to be framed."),
            )?;
            Ok((base_place, expression.with_new_parent(parent), invariant))
        }
    }
}

impl<'a, 'p, 'v: 'p, 'tcx: 'v> IntoSnapshotLowerer<'p, 'v, 'tcx>
    for FramedExpressionToSnapshot<'a>
{
    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl> {
        Ok(vir_low::VariableDecl {
            name: variable.name.clone(),
            ty: self.type_to_snapshot(lowerer, &variable.ty)?,
        })
    }

    // FIXME: Code duplication with
    // prusti-viper/src/encoder/middle/core_proof/snapshots/into_snapshot/pure/mod.rs
    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // In pure contexts values cannot be mutated, so `old` has no effect.
        self.expression_to_snapshot(lowerer, &old.base, expect_math_bool)
    }

    // FIXME: Code duplication with
    // prusti-viper/src/encoder/middle/core_proof/snapshots/into_snapshot/pure/mod.rs
    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let arguments =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
        let func_app = lowerer.call_pure_function_in_pure_context(
            app.get_identifier(),
            arguments,
            return_type,
            app.position,
        )?;
        let result = vir_low::Expression::DomainFuncApp(func_app);
        self.ensure_bool_expression(lowerer, &app.return_type, result, expect_math_bool)
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn owned_non_aliased_snap(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn pointer_deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        _base_snapshot: vir_low::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let (base_place, framed_place, invariant) = self.obtain_invariant(lowerer, &deref.base)?;
        let framed_place = vir_mid::Expression::deref_no_pos(framed_place, deref.ty.clone());
        let deref_fields = lowerer.structural_invariant_to_deref_fields(&invariant)?;
        let base_snapshot = self.expression_to_snapshot(lowerer, base_place, expect_math_bool)?;
        for (deref_place, name, ty) in deref_fields {
            if deref_place == framed_place {
                return lowerer.pointer_target_as_snapshot_field(
                    base_place.get_type(),
                    &name,
                    ty,
                    base_snapshot,
                    deref.position,
                );
            }
        }
        unimplemented!("TODO: A proper error message that failed to find a framing place.")
    }
}
