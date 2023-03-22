use super::super::super::lowerer::Lowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        lifetimes::*,
        lowerer::DomainsLowererInterface,
        references::ReferencesInterface,
        snapshots::{IntoSnapshot, SnapshotDomainsInterface, SnapshotValuesInterface},
        types::TypesInterface,
    },
};
use vir_crate::{
    common::{identifier::WithIdentifier, position::Positioned},
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(super) trait IntoSnapshotLowerer<'p, 'v: 'p, 'tcx: 'v> {
    fn expression_vec_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expressions: &[vir_mid::Expression],
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<Vec<vir_low::Expression>> {
        let mut vec = Vec::new();
        for expression in expressions {
            let snapshot = self.expression_to_snapshot(lowerer, expression, expect_math_bool)?;
            vec.push(snapshot);
        }
        Ok(vec)
    }

    /// `expect_math_bool` argument indicates whether we expect the expression
    /// to be of type mathematical `Bool` or it should be a snapshot bool.
    fn expression_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        expression: &vir_mid::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        match expression {
            vir_mid::Expression::Local(expression) => {
                self.local_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Constructor(expression) => {
                self.constructor_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Variant(expression) => {
                self.variant_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Field(expression) => {
                self.field_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Deref(expression) => {
                self.deref_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::AddrOf(expression) => {
                self.addr_of_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::LabelledOld(expression) => {
                self.labelled_old_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Constant(expression) => {
                self.constant_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::UnaryOp(expression) => {
                self.unary_op_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::BinaryOp(expression) => {
                self.binary_op_to_snapshot(lowerer, expression, expect_math_bool)
            }
            // vir_mid::Expression::ContainerOp(expression) => self.containerop_to_snapshot(lowerer, expression, expect_math_bool),
            // vir_mid::Expression::Seq(expression) => self.seq_to_snapshot(lowerer, expression, expect_math_bool),
            vir_mid::Expression::Conditional(expression) => {
                self.conditional_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Quantifier(expression) => {
                self.quantifier_to_snapshot(lowerer, expression, expect_math_bool)
            }
            // vir_mid::Expression::LetExpr(expression) => self.letexpr_to_snapshot(lowerer, expression, expect_math_bool),
            vir_mid::Expression::FuncApp(expression) => {
                self.func_app_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::BuiltinFuncApp(expression) => {
                self.builtin_func_app_to_snapshot(lowerer, expression, expect_math_bool)
            }
            // vir_mid::Expression::Downcast(expression) => self.downcast_to_snapshot(lowerer, expression, expect_math_bool),
            x => unimplemented!("{:?}", x),
        }
    }

    fn ensure_bool_expression(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        expression: vir_low::Expression,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if expect_math_bool && ty == &vir_mid::Type::Bool {
            let position = expression.position();
            lowerer.obtain_constant_value(ty, expression, position)
        } else {
            Ok(expression)
        }
    }

    fn quantifier_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        quantifier: &vir_mid::Quantifier,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let vir_mid::Quantifier {
            kind,
            variables,
            triggers,
            body,
            position,
        } = quantifier;

        let vars = variables
            .iter()
            .map(|variable| self.variable_to_snapshot(lowerer, variable))
            .collect::<SpannedEncodingResult<Vec<_>>>()?;

        let trigs = triggers
            .iter()
            .map(|trigger| {
                let trig = self
                    .expression_vec_to_snapshot(lowerer, &trigger.terms, expect_math_bool)
                    .unwrap();
                vir_low::Trigger { terms: trig }
            })
            .collect();

        let body = self.expression_to_snapshot(lowerer, body, expect_math_bool)?;

        let kind = match kind {
            vir_mid::expression::QuantifierKind::ForAll => {
                vir_low::expression::QuantifierKind::ForAll
            }
            vir_mid::expression::QuantifierKind::Exists => {
                vir_low::expression::QuantifierKind::Exists
            }
        };

        // no call to ensure_bool_expression since quantifiers are always math bool and forall is built-in to SMT solvers
        Ok(vir_low::Expression::Quantifier(
            vir_low::expression::Quantifier {
                kind,
                variables: vars,
                triggers: trigs,
                body: Box::new(body),
                position: *position,
            },
        ))
    }

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        local: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;

    fn local_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        local: &vir_mid::Local,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let snapshot_variable = self.variable_to_snapshot(lowerer, &local.variable)?;
        let result = vir_low::Expression::local(snapshot_variable, local.position);
        self.ensure_bool_expression(lowerer, local.get_type(), result, expect_math_bool)
    }

    fn constructor_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        constructor: &vir_mid::Constructor,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(!expect_math_bool);
        let mut arguments = Vec::new();
        for argument in &constructor.arguments {
            arguments.push(self.expression_to_snapshot(lowerer, argument, false)?);
        }
        lowerer.construct_struct_snapshot(&constructor.ty, arguments, constructor.position)
    }

    fn variant_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variant: &vir_mid::Variant,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(!expect_math_bool);
        let base_snapshot = self.expression_to_snapshot(lowerer, &variant.base, false)?;
        lowerer.obtain_enum_variant_snapshot(
            variant.base.get_type(),
            &variant.variant_index,
            base_snapshot,
            variant.position,
        )
    }

    fn field_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        field: &vir_mid::Field,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let base_snapshot = self.expression_to_snapshot(lowerer, &field.base, expect_math_bool)?;
        let result = if field.field.is_discriminant() {
            let ty = field.base.get_type();
            // FIXME: Create a method for obtainging the discriminant type.
            let type_decl = lowerer.encoder.get_type_decl_mid(ty)?;
            let enum_decl = type_decl.unwrap_enum();
            let discriminant_call =
                lowerer.obtain_enum_discriminant(base_snapshot, ty, field.position)?;
            lowerer.construct_constant_snapshot(
                &enum_decl.discriminant_type,
                discriminant_call,
                field.position,
            )?
        } else {
            lowerer.obtain_struct_field_snapshot(
                field.base.get_type(),
                &field.field,
                base_snapshot,
                field.position,
            )?
        };
        self.ensure_bool_expression(lowerer, field.get_type(), result, expect_math_bool)
    }

    fn deref_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Deref,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
        let result = lowerer.reference_target_current_snapshot(
            deref.base.get_type(),
            base_snapshot,
            Default::default(),
        )?;
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn addr_of_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        addr_of: &vir_mid::AddrOf,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = match &addr_of.ty {
            vir_mid::Type::Reference(reference) if reference.uniqueness.is_shared() => {
                let base_snapshot =
                    self.expression_to_snapshot(lowerer, &addr_of.base, expect_math_bool)?;
                lowerer.shared_non_alloc_reference_snapshot_constructor(
                    &addr_of.ty,
                    base_snapshot,
                    Default::default(),
                )?
            }
            _ => unimplemented!("ty: {}", addr_of.ty),
        };
        self.ensure_bool_expression(lowerer, &addr_of.ty, result, expect_math_bool)
    }

    fn labelled_old_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        old: &vir_mid::LabelledOld,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    fn constant_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        constant: &vir_mid::Constant,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let low_type = match constant.ty {
            vir_mid::Type::MBool => vir_low::Type::Bool,
            vir_mid::Type::MInt => vir_low::Type::Int,
            vir_mid::Type::MFloat32 => unimplemented!(),
            vir_mid::Type::MFloat64 => unimplemented!(),
            vir_mid::Type::Bool => vir_low::Type::Bool,
            vir_mid::Type::Int(_) => vir_low::Type::Int,
            vir_mid::Type::Float(vir_mid::ty::Float::F32) => {
                vir_low::Type::Float(vir_low::ty::Float::F32)
            }
            vir_mid::Type::Float(vir_mid::ty::Float::F64) => {
                vir_low::Type::Float(vir_low::ty::Float::F64)
            }
            vir_mid::Type::MPerm => vir_low::Type::Perm,
            _ => unimplemented!("constant: {:?}", constant),
        };
        let argument = vir_low::Expression::Constant(vir_low::expression::Constant {
            value: self.constant_value_to_snapshot(lowerer, &constant.value)?,
            ty: low_type,
            position: constant.position,
        });
        let is_already_math_type = matches!(
            constant.ty,
            vir_mid::Type::MBool
                | vir_mid::Type::MInt
                | vir_mid::Type::MFloat32
                | vir_mid::Type::MFloat64
                | vir_mid::Type::MPerm
        );
        if is_already_math_type || (constant.ty == vir_mid::Type::Bool && expect_math_bool) {
            Ok(argument)
        } else {
            lowerer.construct_constant_snapshot(&constant.ty, argument, constant.position)
        }
    }

    fn constant_value_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        value: &vir_mid::expression::ConstantValue,
    ) -> SpannedEncodingResult<vir_low::expression::ConstantValue> {
        let low_value = match value {
            vir_mid::expression::ConstantValue::Bool(value) => {
                vir_low::expression::ConstantValue::Bool(*value)
            }
            vir_mid::expression::ConstantValue::Int(value) => {
                vir_low::expression::ConstantValue::Int(*value)
            }
            vir_mid::expression::ConstantValue::BigInt(value) => {
                vir_low::expression::ConstantValue::BigInt(value.clone())
            }
            vir_mid::expression::ConstantValue::Float(vir_crate::polymorphic::FloatConst::F32(
                value,
            )) => vir_low::expression::ConstantValue::Float32(*value),
            vir_mid::expression::ConstantValue::Float(vir_crate::polymorphic::FloatConst::F64(
                value,
            )) => vir_low::expression::ConstantValue::Float64(*value),
            vir_mid::expression::ConstantValue::FnPtr => {
                unimplemented!();
            }
        };
        Ok(low_value)
    }

    fn unary_op_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::UnaryOp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let argument_snapshot =
            self.expression_to_snapshot(lowerer, &op.argument, expect_math_bool)?;
        let ty = if expect_math_bool && op.get_type() == &vir_mid::Type::Bool {
            &vir_mid::Type::MBool
        } else {
            op.get_type()
        };
        lowerer.construct_unary_op_snapshot(op.op_kind, ty, argument_snapshot, op.position)
    }

    fn unary_op_kind_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::UnaryOpKind,
    ) -> SpannedEncodingResult<vir_low::UnaryOpKind> {
        Ok(match op {
            vir_mid::UnaryOpKind::Not => vir_low::UnaryOpKind::Not,
            vir_mid::UnaryOpKind::Minus => vir_low::UnaryOpKind::Minus,
        })
    }

    fn binary_op_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::BinaryOp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        // FIXME: Binary Operations with MPerm should not be handled manually as special cases
        //   They are difficult because binary operations with MPerm and Integer values are allowed.
        //   Also some of them translate tot PermBinaryOp.
        if let box vir_mid::Expression::Local(local) = &op.left {
            if let box vir_mid::Expression::Constant(constant) = &op.right {
                if let vir_mid::Type::MPerm = local.get_type() {
                    if let vir_mid::Type::MPerm = constant.get_type() {
                        if op.op_kind == vir_mid::BinaryOpKind::Div {
                            let left_snapshot =
                                self.expression_to_snapshot(lowerer, &op.left, false)?;
                            let value =
                                self.constant_value_to_snapshot(lowerer, &constant.value)?;
                            let right_snapshot =
                                vir_low::Expression::constant_no_pos(value, vir_low::ty::Type::Int);
                            return Ok(vir_low::Expression::perm_binary_op(
                                vir_low::ast::expression::PermBinaryOpKind::Div,
                                left_snapshot,
                                right_snapshot,
                                op.position,
                            ));
                        } else if op.op_kind == vir_mid::BinaryOpKind::GtCmp
                            || op.op_kind == vir_mid::BinaryOpKind::LtCmp
                        {
                            let left_snapshot =
                                self.expression_to_snapshot(lowerer, &op.left, false)?;
                            let right_snapshot =
                                self.expression_to_snapshot(lowerer, &op.right, false)?;
                            let arg_type = op.left.get_type();
                            assert_eq!(arg_type, op.right.get_type());
                            return Ok(vir_low::Expression::binary_op(
                                op.op_kind.to_snapshot(lowerer)?,
                                left_snapshot,
                                right_snapshot,
                                op.position,
                            ));
                        }
                    }
                }
            }
        }

        let expect_math_bool_args = expect_math_bool
            && matches!(
                op.op_kind,
                vir_mid::BinaryOpKind::And
                    | vir_mid::BinaryOpKind::Or
                    | vir_mid::BinaryOpKind::Implies
            );
        let ty = if expect_math_bool_args {
            &vir_mid::Type::MBool
        } else {
            op.get_type()
        };
        let left_snapshot =
            self.expression_to_snapshot(lowerer, &op.left, expect_math_bool_args)?;
        let right_snapshot =
            self.expression_to_snapshot(lowerer, &op.right, expect_math_bool_args)?;
        let arg_type = op.left.get_type().clone().erase_lifetimes();
        assert_eq!(arg_type, op.right.get_type().clone().erase_lifetimes());
        let result = lowerer.construct_binary_op_snapshot(
            op.op_kind,
            ty,
            &arg_type,
            left_snapshot,
            right_snapshot,
            op.position,
        )?;
        self.ensure_bool_expression(lowerer, ty, result, expect_math_bool)
    }

    fn binary_op_kind_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        op: &vir_mid::BinaryOpKind,
    ) -> SpannedEncodingResult<vir_low::BinaryOpKind> {
        Ok(match op {
            vir_mid::BinaryOpKind::EqCmp => vir_low::BinaryOpKind::EqCmp,
            vir_mid::BinaryOpKind::NeCmp => vir_low::BinaryOpKind::NeCmp,
            vir_mid::BinaryOpKind::GtCmp => vir_low::BinaryOpKind::GtCmp,
            vir_mid::BinaryOpKind::GeCmp => vir_low::BinaryOpKind::GeCmp,
            vir_mid::BinaryOpKind::LtCmp => vir_low::BinaryOpKind::LtCmp,
            vir_mid::BinaryOpKind::LeCmp => vir_low::BinaryOpKind::LeCmp,
            vir_mid::BinaryOpKind::Add => vir_low::BinaryOpKind::Add,
            vir_mid::BinaryOpKind::Sub => vir_low::BinaryOpKind::Sub,
            vir_mid::BinaryOpKind::Mul => vir_low::BinaryOpKind::Mul,
            vir_mid::BinaryOpKind::Div => vir_low::BinaryOpKind::Div,
            vir_mid::BinaryOpKind::Mod => vir_low::BinaryOpKind::Mod,
            vir_mid::BinaryOpKind::And => vir_low::BinaryOpKind::And,
            vir_mid::BinaryOpKind::Or => vir_low::BinaryOpKind::Or,
            vir_mid::BinaryOpKind::Implies => vir_low::BinaryOpKind::Implies,
            vir_mid::BinaryOpKind::LifetimeIntersection => unreachable!(),
        })
    }

    fn conditional_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        conditional: &vir_mid::Conditional,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let guard_snapshot = self.expression_to_snapshot(lowerer, &conditional.guard, true)?;
        let then_expr_snapshot =
            self.expression_to_snapshot(lowerer, &conditional.then_expr, expect_math_bool)?;
        let else_expr_snapshot =
            self.expression_to_snapshot(lowerer, &conditional.else_expr, expect_math_bool)?;
        let arg_type = conditional.then_expr.get_type();
        assert_eq!(arg_type, conditional.else_expr.get_type());
        // We do not need to ensure expect_math_bool because we pushed this
        // responsibility to the arguments.
        Ok(vir_low::Expression::conditional(
            guard_snapshot,
            then_expr_snapshot,
            else_expr_snapshot,
            conditional.position,
        ))
    }

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    fn builtin_func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_crate::middle::expression::BuiltinFuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::expression::ContainerOpKind;
        use vir_mid::expression::BuiltinFunc;

        let ty_args = app
            .type_arguments
            .iter()
            .map(|ty| self.type_to_snapshot(lowerer, ty))
            .collect::<Result<Vec<_>, _>>()?;
        let mut args =
            self.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
        if !app.arguments.is_empty() {
            let first_arg_type = app.arguments[0].get_type();
            if first_arg_type.is_reference()
                && app.function != vir_mid::BuiltinFunc::SnapshotEquality
            {
                // The first argument is a reference, dereference it.
                args[0] = lowerer.reference_target_current_snapshot(
                    first_arg_type,
                    args[0].clone(),
                    app.position,
                )?;
            }
        }
        lowerer.ensure_type_definition(&app.return_type)?;

        let map = |low_kind| {
            let map_ty = vir_low::Type::map(ty_args[0].clone(), ty_args[1].clone());
            let args = args.clone();
            Ok(vir_low::Expression::container_op(
                low_kind,
                map_ty,
                args,
                app.position,
            ))
        };

        let seq = |low_kind| {
            Ok(vir_low::Expression::container_op(
                low_kind,
                vir_low::Type::seq(ty_args[0].clone()),
                args.clone(),
                app.position,
            ))
        };

        match app.function {
            BuiltinFunc::Size => {
                let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                lowerer.create_domain_func_app(
                    "Size",
                    app.get_identifier(),
                    args,
                    return_type,
                    app.position,
                )
            }
            BuiltinFunc::PaddingSize => {
                assert_eq!(args.len(), 0);
                let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                lowerer.create_domain_func_app(
                    "Size",
                    app.get_identifier(),
                    args,
                    return_type,
                    app.position,
                )
            }
            BuiltinFunc::Discriminant => {
                assert_eq!(args.len(), 1);
                let discriminant_call = lowerer.obtain_enum_discriminant(
                    args.pop().unwrap(),
                    app.arguments[0].get_type(),
                    app.position,
                )?;
                lowerer.construct_constant_snapshot(
                    &app.return_type,
                    discriminant_call,
                    app.position,
                )
            }
            BuiltinFunc::EmptyMap => map(ContainerOpKind::MapEmpty),
            BuiltinFunc::UpdateMap => map(ContainerOpKind::MapUpdate),
            BuiltinFunc::LookupMap => {
                let value = map(ContainerOpKind::MapLookup)?;
                if app.return_type.is_reference() {
                    lowerer.shared_non_alloc_reference_snapshot_constructor(
                        &app.return_type,
                        value,
                        app.position,
                    )
                } else {
                    Ok(value)
                }
            }
            BuiltinFunc::MapLen => {
                let value = map(ContainerOpKind::MapLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::MapContains => {
                let m = map(ContainerOpKind::MapContains)?;
                let m = lowerer.construct_constant_snapshot(app.get_type(), m, app.position)?;
                self.ensure_bool_expression(lowerer, app.get_type(), m, expect_math_bool)
            }
            BuiltinFunc::LookupSeq => {
                use vir_low::operations::ty::Typed;
                assert!(
                    args[0].get_type().is_seq(),
                    "Expected Sequence type, got {:?}",
                    args[0].get_type()
                );
                let value = vir_low::Expression::container_op(
                    ContainerOpKind::SeqIndex,
                    vir_low::Type::seq(ty_args[0].clone()),
                    vec![
                        args[0].clone(),
                        lowerer.obtain_constant_value(
                            app.arguments[1].get_type(),
                            args[1].clone(),
                            args[1].position(),
                        )?,
                    ],
                    app.position,
                );
                if app.return_type.is_reference() {
                    lowerer.shared_non_alloc_reference_snapshot_constructor(
                        &app.return_type,
                        value,
                        app.position,
                    )
                } else {
                    Ok(value)
                }
            }
            BuiltinFunc::ConcatSeq => seq(ContainerOpKind::SeqConcat),
            BuiltinFunc::SeqLen => {
                let value = seq(ContainerOpKind::SeqLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::LifetimeIncluded => {
                assert_eq!(args.len(), 2);
                lowerer.encode_lifetime_included()?;
                Ok(vir_low::Expression::domain_function_call(
                    "Lifetime",
                    "included",
                    args,
                    vir_low::ty::Type::Bool,
                ))
            }
            BuiltinFunc::LifetimeIntersect => {
                assert!(!args.is_empty());
                // FIXME: Fix code duplication.
                let lifetime_set_type = lowerer.lifetime_set_type()?;
                let lifetime_type = lowerer.lifetime_type()?;
                let lifetime_set = vir_low::Expression::container_op_no_pos(
                    vir_low::ContainerOpKind::SetConstructor,
                    lifetime_set_type,
                    args,
                );
                let intersect = lowerer.create_domain_func_app(
                    "Lifetime",
                    "intersect",
                    vec![lifetime_set],
                    lifetime_type,
                    app.position,
                )?;
                Ok(intersect)
            }
            BuiltinFunc::EmptySeq | BuiltinFunc::SingleSeq => {
                Ok(vir_low::Expression::container_op(
                    vir_low::ContainerOpKind::SeqConstructor,
                    vir_low::Type::seq(ty_args[0].clone()),
                    args,
                    app.position,
                ))
            }
            BuiltinFunc::NewInt => {
                assert_eq!(args.len(), 1);
                let arg = args.pop().unwrap();
                let value = lowerer.obtain_constant_value(
                    app.arguments[0].get_type(),
                    arg,
                    app.position,
                )?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::Index => {
                assert_eq!(args.len(), 2);
                // FIXME: Remove duplication with LookupSeq.
                let index = lowerer.obtain_constant_value(
                    app.arguments[1].get_type(),
                    args[1].clone(),
                    app.position,
                )?;
                Ok(vir_low::Expression::container_op(
                    vir_low::ContainerOpKind::SeqIndex,
                    vir_low::Type::seq(ty_args[0].clone()),
                    vec![args[0].clone(), index],
                    app.position,
                ))
            }
            BuiltinFunc::Len => {
                assert_eq!(args.len(), 1);
                // FIXME: Remove duplication with SeqLen.
                let value = seq(ContainerOpKind::SeqLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::SnapshotEquality => {
                assert_eq!(app.arguments[0].get_type(), app.arguments[1].get_type());
                let value = vir_low::Expression::binary_op(
                    vir_low::BinaryOpKind::EqCmp,
                    args[0].clone(),
                    args[1].clone(),
                    app.position,
                );
                if expect_math_bool {
                    Ok(value)
                } else {
                    lowerer.construct_constant_snapshot(&vir_mid::Type::Bool, value, app.position)
                }
            }
        }
    }

    fn type_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
    ) -> SpannedEncodingResult<vir_low::Type> {
        lowerer.ensure_type_definition(ty)?;
        // This ensures that the domain is included into the program.
        lowerer.encode_snapshot_domain_type(ty)
    }
}
