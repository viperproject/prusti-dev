use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        builtin_methods::CallContext,
        footprint::FootprintInterface,
        lowerer::{FunctionsLowererInterface, Lowerer},
        pointers::PointersInterface,
        snapshots::{IntoSnapshotLowerer, SnapshotValuesInterface},
    },
};

use vir_crate::{
    common::{identifier::WithIdentifier, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super::super::super) struct FramedExpressionToSnapshot<'a> {
    framing_variables: &'a [vir_mid::VariableDecl],
}

/// Information needed to convert a pointer dereference into a snapshot.
enum PointerFramingInfo<'e> {
    /// Dereference a single pointer.
    Single {
        /// The place that holds the permission.
        base_place: &'e vir_mid::Expression,
        /// The place framed by the permission in invariant.
        ///
        /// Note: it is rooted at `self` to be able to search for it in the invariant.
        framed_place: vir_mid::Expression,
        /// The invariant of the struct.
        invariant: Vec<vir_mid::Expression>,
    },
    /// Dereference of an element of a range.
    RangeElement { encoded_deref: vir_low::Expression },
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
    ) -> SpannedEncodingResult<PointerFramingInfo<'e>> {
        let ty = expression.get_type();
        if ty.is_struct() {
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            if let vir_mid::TypeDecl::Struct(vir_mid::type_decl::Struct {
                structural_invariant: Some(invariant),
                ..
            }) = type_decl
            {
                let self_place = vir_mid::VariableDecl::self_variable(ty.clone());
                Ok(PointerFramingInfo::Single {
                    base_place: expression,
                    framed_place: self_place.into(),
                    invariant,
                })
            } else {
                unimplemented!("TODO: A proper error message that only permissions from non-nested structs are supported.");
            }
        } else if let vir_mid::Expression::BuiltinFuncApp(vir_mid::BuiltinFuncApp {
            function:
                vir_mid::BuiltinFunc::PtrOffset
                | vir_mid::BuiltinFunc::PtrWrappingOffset
                | vir_mid::BuiltinFunc::PtrAddressOffset,
            type_arguments: _,
            arguments,
            return_type: _,
            position,
        }) = expression
        {
            let  PointerFramingInfo::Single {base_place, framed_place, invariant} = self.obtain_invariant(
                lowerer,
                &arguments[0],
            )? else {
                unimplemented!("expression: {expression}");
            };
            let (_, deref_range_fields) =
                lowerer.structural_invariant_to_deref_fields(&invariant)?;
            let deref_range_field = deref_range_fields
                .into_iter()
                .find(|deref_range_field| deref_range_field.address == framed_place)
                .unwrap();
            // for deref_range_field in deref_range_fields {
            //     unimplemented!("TODO: {}", deref_range_field.address);
            // }
            let base_snapshot = self.expression_to_snapshot(lowerer, base_place, false)?;
            let index_snapshot = self.expression_to_snapshot(lowerer, &arguments[1], false)?;
            let index_int = lowerer.obtain_constant_value(
                arguments[1].get_type(),
                index_snapshot,
                *position,
            )?;
            // let seq_type = vir_low::Type::seq(deref_range_field.field_type);
            let seq_type = deref_range_field.field_type;
            let pointer_deref = lowerer.pointer_target_as_snapshot_field(
                base_place.get_type(),
                &deref_range_field.field_name,
                seq_type.clone(),
                base_snapshot,
                *position,
            )?;
            let element = vir_low::Expression::container_op(
                vir_low::ContainerOpKind::SeqIndex,
                seq_type,
                vec![pointer_deref, index_int],
                *position,
            );
            Ok(PointerFramingInfo::RangeElement {
                encoded_deref: element,
            })
            // let expression_with_new_parent = vir_mid::Expression::builtin_func_app(
            //     vir_mid::BuiltinFunc::PtrWrappingOffset,
            //     type_arguments.clone(),
            //     vec![parent.into(), arguments[1].clone()],
            //     return_type.clone(),
            //     *position,
            // );
            // Ok((base_place, expression_with_new_parent, invariant))
        } else {
            let  PointerFramingInfo::Single {base_place, framed_place, invariant} = self.obtain_invariant(
                lowerer,
                expression
                    .get_parent_ref()
                    .expect("TODO: A proper error message that the permission has to be framed."),
            )? else {
                unimplemented!("expression: {expression}");
            };
            Ok(PointerFramingInfo::Single {
                base_place,
                framed_place: expression.with_new_parent(framed_place),
                invariant,
            })
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
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _acc_predicate: &vir_mid::AccPredicate,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        todo!()
    }

    fn call_context(&self) -> CallContext {
        todo!()
    }

    fn owned_non_aliased_snap(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _ty: &vir_mid::Type,
        _pointer_place: &vir_mid::Expression,
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
        // let (base_place, framed_place, invariant) = self.obtain_invariant(lowerer, &deref.base)?;
        match self.obtain_invariant(lowerer, &deref.base)? {
            PointerFramingInfo::Single {
                base_place,
                framed_place,
                invariant,
            } => {
                let framed_place =
                    vir_mid::Expression::deref_no_pos(framed_place, deref.ty.clone());
                let (deref_fields, _) = lowerer.structural_invariant_to_deref_fields(&invariant)?;
                let base_snapshot =
                    self.expression_to_snapshot(lowerer, base_place, expect_math_bool)?;
                // for (deref_place, name, ty) in deref_fields {
                for deref_field in deref_fields {
                    if deref_field.place == framed_place {
                        return lowerer.pointer_target_as_snapshot_field(
                            base_place.get_type(),
                            &deref_field.field_name,
                            deref_field.field_type,
                            base_snapshot,
                            deref.position,
                        );
                    }
                }
            }
            PointerFramingInfo::RangeElement { encoded_deref } => {
                return Ok(encoded_deref);
            }
        }
        // let framed_place = vir_mid::Expression::deref_no_pos(framed_place, deref.ty.clone());
        // let (deref_fields, deref_range_fields) =
        //     lowerer.structural_invariant_to_deref_fields(&invariant)?;
        // let base_snapshot = self.expression_to_snapshot(lowerer, base_place, expect_math_bool)?;
        // // for (deref_place, name, ty) in deref_fields {
        // for deref_field in deref_fields {
        //     if deref_field.place == framed_place {
        //         return lowerer.pointer_target_as_snapshot_field(
        //             base_place.get_type(),
        //             &deref_field.field_name,
        //             deref_field.field_type,
        //             base_snapshot,
        //             deref.position,
        //         );
        //     }
        // }
        // for deref_range_field in deref_range_fields {
        //     unimplemented!("TODO: {}", deref_range_field.address);
        // }
        unimplemented!("TODO: A proper error message that failed to find a framing place.")
    }

    fn push_bound_variables(
        &mut self,
        _variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()> {
        todo!()
    }

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()> {
        todo!()
    }
}
