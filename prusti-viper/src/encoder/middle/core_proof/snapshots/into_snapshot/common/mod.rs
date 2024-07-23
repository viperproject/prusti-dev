use super::super::super::lowerer::Lowerer;
use crate::encoder::{
    errors::SpannedEncodingResult,
    high::types::HighTypeEncoderInterface,
    middle::core_proof::{
        addresses::AddressesInterface,
        arithmetic_wrappers::ArithmeticWrappersInterface,
        builtin_methods::CallContext,
        casts::CastsInterface,
        lifetimes::*,
        lowerer::DomainsLowererInterface,
        places::PlacesInterface,
        pointers::PointersInterface,
        predicates::{PredicatesMemoryBlockInterface, PredicatesOwnedInterface},
        references::ReferencesInterface,
        snapshots::{
            IntoSnapshot, SnapshotDomainsInterface, SnapshotValidityInterface,
            SnapshotValuesInterface,
        },
        type_layouts::TypeLayoutsInterface,
        types::TypesInterface,
    },
};
use prusti_common::config;
use vir_crate::{
    common::{
        builtin_constants::LIFETIME_DOMAIN_NAME,
        expression::{BinaryOperationHelpers, ExpressionIterator},
        identifier::WithIdentifier,
        position::Positioned,
        validator::Validator,
    },
    low::{self as vir_low},
    middle::{self as vir_mid, operations::ty::Typed},
};

pub(in super::super::super) trait IntoSnapshotLowerer<'p, 'v: 'p, 'tcx: 'v>:
    Sized
{
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
        self.expression_to_snapshot_impl(lowerer, expression, expect_math_bool)
    }

    fn expression_to_snapshot_impl(
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
            vir_mid::Expression::Final(expression) => {
                self.final_to_snapshot(lowerer, expression, expect_math_bool)
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
            vir_mid::Expression::AccPredicate(expression) => {
                self.acc_predicate_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::Unfolding(expression) => {
                self.unfolding_to_snapshot(lowerer, expression, expect_math_bool)
            }
            vir_mid::Expression::EvalIn(expression) => self.eval_in_to_snapshot(
                lowerer,
                expression,
                expect_math_bool,
                Self::expression_to_snapshot,
            ),
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

    fn variable_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        variable: &vir_mid::VariableDecl,
    ) -> SpannedEncodingResult<vir_low::VariableDecl>;

    fn local_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        local: &vir_mid::Local,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        self.local_to_snapshot_impl(lowerer, local, expect_math_bool)
    }

    fn local_to_snapshot_impl(
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
        let struct_snapshot =
            lowerer.construct_struct_snapshot(&constructor.ty, arguments, constructor.position)?;
        if let vir_mid::Type::Enum(vir_mid::ty::Enum {
            variant: Some(_), ..
        }) = &constructor.ty
        {
            let enum_snapshot = lowerer.construct_enum_snapshot(
                &constructor.ty,
                struct_snapshot,
                constructor.position,
            )?;
            Ok(enum_snapshot)
        } else {
            Ok(struct_snapshot)
        }
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
        self.field_to_snapshot_impl(lowerer, field, expect_math_bool)
    }

    fn field_to_snapshot_impl(
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
        } else if field.field.is_address() {
            lowerer.pointer_address(&field.field.ty, base_snapshot, field.position)?
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
        let ty = deref.base.get_type();
        let result = if ty.is_reference() {
            lowerer.reference_target_current_snapshot(ty, base_snapshot, deref.position)?
        } else {
            self.pointer_deref_to_snapshot(lowerer, deref, base_snapshot, expect_math_bool)?
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn final_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        deref: &vir_mid::Final,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let base_snapshot = self.expression_to_snapshot(lowerer, &deref.base, expect_math_bool)?;
        let ty = deref.base.get_type();
        let result = if ty.is_reference() {
            lowerer.reference_target_final_snapshot(ty, base_snapshot, deref.position)?
        } else {
            unreachable!("Final deref is not supported for non-reference types.")
        };
        self.ensure_bool_expression(lowerer, deref.get_type(), result, expect_math_bool)
    }

    fn pointer_deref_to_snapshot(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _deref: &vir_mid::Deref,
        _base_snapshot: vir_low::Expression,
        _expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unreachable!("Should be overriden.");
    }

    fn addr_of_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        addr_of: &vir_mid::AddrOf,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let result = match &addr_of.ty {
            vir_mid::Type::Reference(reference) if reference.uniqueness.is_shared() => {
                let base_snapshot = self.expression_to_snapshot(lowerer, &addr_of.base, false)?;
                lowerer.shared_non_alloc_reference_snapshot_constructor(
                    &addr_of.ty,
                    base_snapshot,
                    Default::default(),
                )?
            }
            _ => unimplemented!("addr_of: {addr_of}\n{addr_of:?}\n ty: {}", addr_of.ty),
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
            vir_mid::expression::ConstantValue::String(_value) => {
                unimplemented!();
            }
            vir_mid::expression::ConstantValue::Float(_value) => {
                unimplemented!();
            }
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
        self.binary_op_to_snapshot_impl(lowerer, op, expect_math_bool)
    }

    fn binary_op_to_snapshot_impl(
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
        if expect_math_bool && op.op_kind == vir_mid::BinaryOpKind::EqCmp {
            // FIXME: Instead of this ad-hoc optimization, have a proper
            // optimization pass.
            Ok(vir_low::Expression::binary_op(
                vir_low::BinaryOpKind::EqCmp,
                left_snapshot,
                right_snapshot,
                op.position,
            ))
        } else {
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
        let arg_type = vir_low::operations::ty::Typed::get_type(&then_expr_snapshot);
        assert_eq!(
            arg_type,
            vir_low::operations::ty::Typed::get_type(&else_expr_snapshot)
        );
        // We do not need to ensure expect_math_bool because we pushed this
        // responsibility to the arguments.
        Ok(vir_low::Expression::conditional(
            guard_snapshot,
            then_expr_snapshot,
            else_expr_snapshot,
            conditional.position,
        ))
    }

    fn quantifier_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        quantifier: &vir_mid::Quantifier,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool);
        let quantifier_kind = match quantifier.kind {
            vir_mid::expression::QuantifierKind::ForAll => {
                vir_low::expression::QuantifierKind::ForAll
            }
            vir_mid::expression::QuantifierKind::Exists => {
                vir_low::expression::QuantifierKind::Exists
            }
        };
        self.push_bound_variables(&quantifier.variables)?;
        let body_snapshot = self.expression_to_snapshot(lowerer, &quantifier.body, true)?;
        let mut variables = Vec::new();
        let mut variable_validity = Vec::new();
        for variable_mid in &quantifier.variables {
            let variable = vir_low::VariableDecl::new(
                variable_mid.name.clone(),
                self.type_to_snapshot(lowerer, &variable_mid.ty)?,
            );
            variables.push(variable.clone());
            let validity =
                lowerer.encode_snapshot_valid_call_for_type(variable.into(), &variable_mid.ty)?;
            variable_validity.push(validity);
        }
        let variable_validity = variable_validity.into_iter().conjoin();
        let body = match quantifier.kind {
            vir_mid::expression::QuantifierKind::ForAll => {
                vir_low::Expression::implies(variable_validity, body_snapshot)
            }
            vir_mid::expression::QuantifierKind::Exists => {
                vir_low::Expression::and(variable_validity, body_snapshot)
            }
        };
        let triggers = quantifier
            .triggers
            .iter()
            .map(|trigger| {
                trigger
                    .terms
                    .iter()
                    .map(|expr| self.expression_to_snapshot(lowerer, expr, true))
                    .collect::<SpannedEncodingResult<Vec<_>>>()
                    .map(vir_low::Trigger::new)
            })
            .collect::<SpannedEncodingResult<Vec<_>>>()?;
        let result = vir_low::Expression::quantifier(
            None,
            quantifier_kind,
            variables,
            triggers,
            body,
            quantifier.position,
        );
        self.pop_bound_variables()?;
        // self.ensure_bool_expression(lowerer, &vir_mid::Type::Bool, result, expect_math_bool)
        Ok(result)
    }

    fn push_bound_variables(
        &mut self,
        variables: &[vir_mid::VariableDecl],
    ) -> SpannedEncodingResult<()>;

    fn pop_bound_variables(&mut self) -> SpannedEncodingResult<()>;

    fn func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::FuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    fn builtin_func_app_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        app: &vir_mid::BuiltinFuncApp,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        use vir_low::expression::ContainerOpKind;
        use vir_mid::expression::BuiltinFunc;

        let ty_args = app
            .type_arguments
            .iter()
            .map(|ty| self.type_to_snapshot(lowerer, ty))
            .collect::<Result<Vec<_>, _>>()?;
        let construct_args = |this: &mut Self, lowerer: &mut _| -> Result<_, _> {
            let mut args =
                this.expression_vec_to_snapshot(lowerer, &app.arguments, expect_math_bool)?;
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
            Ok(args)
        };
        lowerer.ensure_type_definition(&app.return_type)?;

        let map = |this, lowerer, low_kind| {
            let map_ty = vir_low::Type::map(ty_args[0].clone(), ty_args[1].clone());
            let args = construct_args(this, lowerer)?;
            Ok(vir_low::Expression::container_op(
                low_kind,
                map_ty,
                args,
                app.position,
            ))
        };

        let seq = |this, lowerer, low_kind| {
            let args = construct_args(this, lowerer)?;
            Ok(vir_low::Expression::container_op(
                low_kind,
                vir_low::Type::seq(ty_args[0].clone()),
                args,
                app.position,
            ))
        };

        match app.function {
            BuiltinFunc::Size => {
                let _return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                let args = construct_args(self, lowerer)?;
                assert_eq!(app.type_arguments.len(), 1);
                match &app.type_arguments[0] {
                    vir_mid::Type::Int(ty)
                        if !matches!(
                            ty,
                            vir_mid::ty::Int::Isize
                                | vir_mid::ty::Int::Usize
                                | vir_mid::ty::Int::Char
                                | vir_mid::ty::Int::Unbounded
                        ) =>
                    {
                        let size = match ty {
                            vir_mid::ty::Int::I8 => 1,
                            vir_mid::ty::Int::I16 => 2,
                            vir_mid::ty::Int::I32 => 4,
                            vir_mid::ty::Int::I64 => 8,
                            vir_mid::ty::Int::I128 => 16,
                            vir_mid::ty::Int::U8 => 1,
                            vir_mid::ty::Int::U16 => 2,
                            vir_mid::ty::Int::U32 => 4,
                            vir_mid::ty::Int::U64 => 8,
                            vir_mid::ty::Int::U128 => 16,
                            vir_mid::ty::Int::Isize => unreachable!(),
                            vir_mid::ty::Int::Usize => unreachable!(),
                            vir_mid::ty::Int::Char => unreachable!(),
                            vir_mid::ty::Int::Unbounded => unreachable!(),
                        };
                        let constant =
                            vir_low::Expression::constant_no_pos(size.into(), vir_low::Type::Int);
                        lowerer.construct_constant_snapshot(
                            &app.return_type,
                            constant,
                            app.position,
                        )
                    }
                    vir_mid::Type::Bool => {
                        let size = 1;
                        let constant =
                            vir_low::Expression::constant_no_pos(size.into(), vir_low::Type::Int);
                        lowerer.construct_constant_snapshot(
                            &app.return_type,
                            constant,
                            app.position,
                        )
                    }
                    vir_mid::Type::Struct(_ty) => {
                        let type_decl = lowerer
                            .encoder
                            .get_type_decl_mid(&app.type_arguments[0])?
                            .unwrap_struct();
                        if let Some(size) = type_decl.size {
                            let constant = vir_low::Expression::constant_no_pos(
                                size.into(),
                                vir_low::Type::Int,
                            );
                            lowerer.construct_constant_snapshot(
                                &app.return_type,
                                constant,
                                app.position,
                            )
                        } else {
                            lowerer.encode_size_function_call_with_axioms(
                                app.get_identifier(),
                                args,
                                app.position,
                            )
                            // lowerer.create_domain_func_app(
                            //     "Size",
                            //     app.get_identifier(),
                            //     args,
                            //     return_type,
                            //     app.position,
                            // )
                        }
                    }
                    // _ => lowerer.create_domain_func_app(
                    //     "Size",
                    //     app.get_identifier(),
                    //     args,
                    //     return_type,
                    //     app.position,
                    // ),
                    _ => lowerer.encode_size_function_call_with_axioms(
                        app.get_identifier(),
                        args,
                        app.position,
                    ),
                }
            }
            BuiltinFunc::PaddingSize => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 0);
                // let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                // lowerer.create_domain_func_app(
                //     "Size",
                //     app.get_identifier(),
                //     args,
                //     return_type,
                //     app.position,
                // )
                lowerer.encode_size_function_call_with_axioms(
                    app.get_identifier(),
                    args,
                    app.position,
                )
            }
            BuiltinFunc::Align => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 0);
                let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                assert_eq!(app.type_arguments.len(), 1);
                match app.type_arguments[0] {
                    vir_mid::Type::Int(ty)
                        if !matches!(
                            ty,
                            vir_mid::ty::Int::Isize
                                | vir_mid::ty::Int::Usize
                                | vir_mid::ty::Int::Char
                                | vir_mid::ty::Int::Unbounded
                        ) =>
                    {
                        let size = match ty {
                            vir_mid::ty::Int::I8 => 1,
                            vir_mid::ty::Int::I16 => 2,
                            vir_mid::ty::Int::I32 => 4,
                            vir_mid::ty::Int::I64 => 8,
                            vir_mid::ty::Int::I128 => 8,
                            vir_mid::ty::Int::U8 => 1,
                            vir_mid::ty::Int::U16 => 2,
                            vir_mid::ty::Int::U32 => 4,
                            vir_mid::ty::Int::U64 => 8,
                            vir_mid::ty::Int::U128 => 8,
                            vir_mid::ty::Int::Isize => unreachable!(),
                            vir_mid::ty::Int::Usize => unreachable!(),
                            vir_mid::ty::Int::Char => unreachable!(),
                            vir_mid::ty::Int::Unbounded => unreachable!(),
                        };
                        let constant =
                            vir_low::Expression::constant_no_pos(size.into(), vir_low::Type::Int);
                        lowerer.construct_constant_snapshot(
                            &app.return_type,
                            constant,
                            app.position,
                        )
                    }
                    _ => lowerer.create_domain_func_app(
                        "Align",
                        app.get_identifier(),
                        args,
                        return_type,
                        app.position,
                    ),
                }
            }
            BuiltinFunc::Discriminant => {
                let mut args = construct_args(self, lowerer)?;
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
            BuiltinFunc::EmptyMap => map(self, lowerer, ContainerOpKind::MapEmpty),
            BuiltinFunc::UpdateMap => map(self, lowerer, ContainerOpKind::MapUpdate),
            BuiltinFunc::LookupMap => {
                let value = map(self, lowerer, ContainerOpKind::MapLookup)?;
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
                let value = map(self, lowerer, ContainerOpKind::MapLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::MapContains => {
                let m = map(self, lowerer, ContainerOpKind::MapContains)?;
                let m = lowerer.construct_constant_snapshot(app.get_type(), m, app.position)?;
                self.ensure_bool_expression(lowerer, app.get_type(), m, expect_math_bool)
            }
            BuiltinFunc::LookupSeq => {
                use vir_low::operations::ty::Typed;
                let args = construct_args(self, lowerer)?;
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
            BuiltinFunc::ConcatSeq => seq(self, lowerer, ContainerOpKind::SeqConcat),
            BuiltinFunc::SeqLen => {
                let value = seq(self, lowerer, ContainerOpKind::SeqLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::LifetimeIncluded => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 2);
                lowerer.encode_lifetime_included()?;
                Ok(vir_low::Expression::domain_function_call(
                    LIFETIME_DOMAIN_NAME,
                    "included",
                    args,
                    vir_low::ty::Type::Bool,
                ))
            }
            BuiltinFunc::LifetimeIntersect => {
                let args = construct_args(self, lowerer)?;
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
                    LIFETIME_DOMAIN_NAME,
                    "intersect",
                    vec![lifetime_set],
                    lifetime_type,
                    app.position,
                )?;
                Ok(intersect)
            }
            BuiltinFunc::EmptySeq | BuiltinFunc::SingleSeq => {
                let args = construct_args(self, lowerer)?;
                Ok(vir_low::Expression::container_op(
                    vir_low::ContainerOpKind::SeqConstructor,
                    vir_low::Type::seq(ty_args[0].clone()),
                    args,
                    app.position,
                ))
            }
            BuiltinFunc::NewInt => {
                let mut args = construct_args(self, lowerer)?;
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
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 2);
                // FIXME: Remove duplication with LookupSeq.
                let index = lowerer.obtain_constant_value(
                    app.arguments[1].get_type(),
                    args[1].clone(),
                    app.position,
                )?;
                let expression = vir_low::Expression::container_op(
                    vir_low::ContainerOpKind::SeqIndex,
                    vir_low::Type::seq(ty_args[0].clone()),
                    vec![args[0].clone(), index],
                    app.position,
                );
                expression.assert_valid_debug();
                Ok(expression)
            }
            BuiltinFunc::Len => {
                assert_eq!(app.arguments.len(), 1);
                // FIXME: Remove duplication with SeqLen.
                let value = seq(self, lowerer, ContainerOpKind::SeqLen)?;
                lowerer.construct_constant_snapshot(app.get_type(), value, app.position)
            }
            BuiltinFunc::SnapshotEquality => {
                assert_eq!(app.arguments[0].get_type(), app.arguments[1].get_type());
                let args = construct_args(self, lowerer)?;
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
            BuiltinFunc::PtrIsNull => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 1);
                let ty = app.arguments[0].get_type();
                let address = lowerer.pointer_address(ty, args[0].clone(), app.position)?;
                let null_address = lowerer.address_null(app.position)?;
                let equals = vir_low::Expression::equals(address, null_address);
                let equals =
                    lowerer.construct_constant_snapshot(app.get_type(), equals, app.position)?;
                self.ensure_bool_expression(lowerer, app.get_type(), equals, expect_math_bool)
            }
            BuiltinFunc::PtrOffset
            | BuiltinFunc::PtrWrappingOffset
            | BuiltinFunc::PtrAdd
            | BuiltinFunc::PtrAddressOffset => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 2);
                let ty = app.arguments[0].get_type();
                let address = lowerer.pointer_address(ty, args[0].clone(), app.position)?;
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                let size = lowerer.encode_type_size_expression2(
                    &pointer_type.target_type,
                    &*pointer_type.target_type,
                )?;
                let offset = lowerer.obtain_constant_value(
                    app.arguments[1].get_type(),
                    args[1].clone(),
                    app.position,
                )?;
                let new_address = lowerer.address_offset(size, address, offset, app.position)?;
                lowerer.address_to_pointer(ty, new_address, app.position)
            }
            BuiltinFunc::PtrAddressOffsetFrom => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 2);
                let ty = app.arguments[0].get_type();
                let address_to = lowerer.pointer_address(ty, args[0].clone(), app.position)?;
                let address_from = lowerer.pointer_address(ty, args[1].clone(), app.position)?;
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                let size = lowerer.encode_type_size_expression2(
                    &pointer_type.target_type,
                    &*pointer_type.target_type,
                )?;
                let offset =
                    lowerer.offset_from_address(size, address_to, address_from, app.position)?;
                lowerer.construct_constant_snapshot(
                    &vir_mid::Type::Int(vir_mid::ty::Int::Unbounded),
                    offset,
                    app.position,
                )
            }
            BuiltinFunc::PtrSameAllocation => {
                let args = construct_args(self, lowerer)?;
                let ty = app.arguments[0].get_type();
                assert_eq!(args.len(), 2);
                let address1 = lowerer.pointer_address(ty, args[0].clone(), app.position)?;
                let address2 = lowerer.pointer_address(ty, args[1].clone(), app.position)?;
                let allocation1 = lowerer.address_allocation(address1, app.position)?;
                let allocation2 = lowerer.address_allocation(address2, app.position)?;
                let equals = vir_low::Expression::equals(allocation1, allocation2);
                let equals =
                    lowerer.construct_constant_snapshot(app.get_type(), equals, app.position)?;
                self.ensure_bool_expression(lowerer, app.get_type(), equals, expect_math_bool)
            }
            BuiltinFunc::PtrRangeContains => {
                let args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 3);
                let ty = app.arguments[0].get_type();
                let start_address = lowerer.pointer_address(ty, args[0].clone(), app.position)?;
                let vir_mid::Type::Pointer(pointer_type) = ty else {
                    unreachable!()
                };
                let type_size = lowerer.encode_type_size_expression2(
                    &pointer_type.target_type,
                    &*pointer_type.target_type,
                )?;
                let range_length = lowerer.obtain_constant_value(
                    app.arguments[1].get_type(),
                    args[1].clone(),
                    app.position,
                )?;
                let checked_address = lowerer.pointer_address(ty, args[2].clone(), app.position)?;
                lowerer.pointer_range_contains(
                    start_address,
                    type_size,
                    range_length,
                    checked_address,
                    app.position,
                )
            }
            BuiltinFunc::IsValid => {
                let mut args = construct_args(self, lowerer)?;
                assert_eq!(app.arguments.len(), 1);
                let argument = args.pop().unwrap();
                let ty = app.arguments[0].get_type();
                lowerer.encode_snapshot_valid_call_for_type(argument, ty)
            }
            BuiltinFunc::EnsureOwnedPredicate => {
                assert_eq!(app.arguments.len(), 1);
                fn peel_unfolding<'p, 'v: 'p, 'tcx: 'v>(
                    lowerer: &mut Lowerer<'p, 'v, 'tcx>,
                    into_snap_lowerer: &mut impl IntoSnapshotLowerer<'p, 'v, 'tcx>,
                    place: &vir_mid::Expression,
                ) -> SpannedEncodingResult<vir_low::Expression> {
                    match place {
                        vir_mid::Expression::Unfolding(unfolding) => {
                            let body = peel_unfolding(lowerer, into_snap_lowerer, &unfolding.body)?;
                            into_snap_lowerer.unfolding_to_snapshot_with_body(
                                lowerer,
                                &unfolding.predicate,
                                body,
                                unfolding.position,
                                true,
                            )
                        }
                        _ => {
                            let ty = place.get_type();
                            let snap_call =
                                into_snap_lowerer.owned_non_aliased_snap(lowerer, ty, place)?;
                            let snapshot =
                                into_snap_lowerer.expression_to_snapshot(lowerer, place, true)?;
                            let position = place.position();
                            Ok(vir_low::Expression::binary_op(
                                vir_low::BinaryOpKind::EqCmp,
                                snap_call,
                                snapshot,
                                position,
                            ))
                        }
                    }
                }
                peel_unfolding(lowerer, self, &app.arguments[0])
                // let argument = &app.arguments[0];
                // let ty = argument.get_type();
                // let snap_call = self.owned_non_aliased_snap(lowerer, ty, argument)?;
                // lowerer.wrap_snap_into_bool(ty, snap_call.set_default_position(app.position))
            }
            BuiltinFunc::TakeLifetime => {
                unimplemented!("TODO: Delete");
            }
            BuiltinFunc::ReadByte => {
                let mut args = construct_args(self, lowerer)?;
                let index = args.pop().unwrap();
                let bytes = args.pop().unwrap();
                lowerer.encode_read_byte_expression_usize(bytes, index, app.position)
            }
            BuiltinFunc::MemoryBlockBytes => {
                assert_eq!(app.arguments.len(), 2);
                // let mut args = construct_args(self, lowerer)?;
                // let size = args.pop().unwrap();
                let size =
                    self.expression_to_snapshot(lowerer, &app.arguments[1], expect_math_bool)?;
                // let pointer_value = args.pop().unwrap();
                // let address = lowerer.pointer_address(
                //     app.arguments[0].get_type(),
                //     pointer_value,
                //     app.position,
                // )?;
                let address = self.pointer_deref_into_address(lowerer, &app.arguments[0])?;
                lowerer.encode_memory_block_bytes_expression(address, size)
            }
            BuiltinFunc::MemoryBlockBytesPtr => {
                // TODO: Should have been desugared into MemoryBlockBytes.
                let pointer = &app.arguments[0];
                let vir_mid::Type::Pointer(pointer_type) = pointer.get_type()  else {
                    unreachable!("pointer.get_type() should be Pointer, got: {}", pointer.get_type());
                };
                let pointer_deref = pointer
                    .clone()
                    .deref((*pointer_type.target_type).clone(), app.position);
                let size =
                    self.expression_to_snapshot(lowerer, &app.arguments[1], expect_math_bool)?;
                let address = self.pointer_deref_into_address(lowerer, &pointer_deref)?;
                lowerer.encode_memory_block_bytes_expression(address, size)
            }
            BuiltinFunc::DerefOwn => {
                let mut args = construct_args(self, lowerer)?;
                let pointer_type = app.arguments[0].get_type();
                // let address = lowerer.pointer_address(
                //     pointer_type,
                //     args[0].clone(),
                //     app.position,
                // )?;
                let index = args.pop().unwrap();
                let pointer = args.pop().unwrap();
                self.deref_own(lowerer, pointer_type, pointer, index, app.position)
            }
            BuiltinFunc::CastMutToConstPointer => {
                let mut args = construct_args(self, lowerer)?;
                // We currently do not distinguish between mutable and immutable
                // pointers so this is a no-op.
                Ok(args.pop().unwrap())
                // let address = lowerer.pointer_address(
                //     app.arguments[0].get_type(),
                //     args[0].clone(),
                //     app.position,
                // )?;
                // lowerer.address_to_pointer(&app.return_type, address, app.position)
            }
            BuiltinFunc::CastPtrToPtr => {
                let mut args = construct_args(self, lowerer)?;
                // FIXME: This encoding is probably wrong because we are not doing any casting.
                Ok(args.pop().unwrap())
            }
            BuiltinFunc::CastIntToInt => {
                let mut args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 1);
                let arg = args.pop().unwrap();
                assert_eq!(app.type_arguments.len(), 2);
                let source_type = &app.type_arguments[0];
                let destination_type = &app.type_arguments[1];
                lowerer.cast_int_to_int(source_type, destination_type, arg, app.position)
            }
            BuiltinFunc::BeforeExpiry => {
                unreachable!("BeforeExpiry should be desugard before");
            }
            BuiltinFunc::AfterExpiry => {
                unreachable!("AfterExpiry should be desugard before");
            }
            BuiltinFunc::BuildingUniqueRefPredicate => {
                unreachable!("UniqueRef should have been already built.")
            }
            BuiltinFunc::BuildingUniqueRefPredicateWithRealLifetime
            | BuiltinFunc::BuildingUniqueRefPredicateRangeWithRealLifetime => {
                unreachable!("UniqueRef should have been already built.")
            }
            BuiltinFunc::BuildingFracRefPredicate => {
                unreachable!("FracRef should have been already built.")
            }
            BuiltinFunc::AllocationNeverFails => {
                let return_type = self.type_to_snapshot(lowerer, &app.return_type)?;
                let call = lowerer.create_domain_func_app(
                    "AllocationNeverFails",
                    "allocation_never_fails",
                    Vec::new(),
                    return_type,
                    app.position,
                )?;
                self.ensure_bool_expression(lowerer, app.get_type(), call, expect_math_bool)
            }
            BuiltinFunc::Multiply => {
                let mut args = construct_args(self, lowerer)?;
                assert_eq!(args.len(), 2);
                let arg1 = args.pop().unwrap();
                let arg2 = args.pop().unwrap();
                let arg1 = lowerer.obtain_constant_value(
                    app.arguments[0].get_type(),
                    arg1,
                    app.position,
                )?;
                let arg2 = lowerer.obtain_constant_value(
                    app.arguments[1].get_type(),
                    arg2,
                    app.position,
                )?;
                let expression = if config::smt_use_nonlinear_arithmetic_solver() {
                    vir_low::Expression::multiply(arg1, arg2)
                } else {
                    // let multiply_call = lowerer.create_domain_func_app(
                    //     "ArithmeticWrappers",
                    //     "multiply_wrapper",
                    //     vec![arg1, arg2],
                    //     vir_low::ty::Type::Int,
                    //     app.position,
                    // )?;
                    let multiply_call = lowerer.int_mul_call(arg1, arg2, app.position)?;
                    lowerer.construct_constant_snapshot(
                        &app.return_type,
                        multiply_call,
                        app.position,
                    )?
                    // let unbounded_ty = vir_mid::Type::Int(vir_mid::ty::Int::Unbounded);
                    // let return_type = self.type_to_snapshot(lowerer, &unbounded_ty)?;
                    // let is_not_unbounded = !matches!(app.return_type, vir_mid::Type::Int(vir_mid::ty::Int::Unbounded));
                    // if is_not_unbounded {
                    //     // arg1 = lowerer.cast_int_to_int(&app.return_type, &unbounded_ty, arg1, app.position)?;
                    //     // arg2 = lowerer.cast_int_to_int(&app.return_type, &unbounded_ty, arg2, app.position)?;
                    //     arg1 = lowerer.obtain_constant_value(&app.return_type, arg1, app.position)?;
                    // }
                    // let mut call = lowerer.create_domain_func_app(
                    //     "ArithmeticWrappers",
                    //     "multiply_wrapper",
                    //     vec![arg1, arg2],
                    //     return_type,
                    //     app.position,
                    // )?;
                    // if is_not_unbounded {
                    //     call = lowerer.cast_int_to_int(&unbounded_ty, &app.return_type, call, app.position)?;
                    // }
                    // call
                };
                Ok(expression)
            }
        }
    }

    /// Deref a raw pointer with the specified offset.
    fn deref_own(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _pointer_type: &vir_mid::Type,
        _pointer: vir_low::Expression,
        _index: vir_low::Expression,
        _position: vir_low::Position,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        unimplemented!();
    }

    // FIXME: Code duplication.
    fn pointer_deref_into_address(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        if let vir_mid::Expression::EvalIn(eval_in) = place {
            let result =
                self.eval_in_to_snapshot(lowerer, eval_in, false, |this, lowerer, place, _| {
                    this.pointer_deref_into_address(lowerer, place)
                });
            return result;
        }
        if let Some(parent) = place.get_parent_ref_of_place_like() {
            let parent_type = parent.get_type();
            if place.is_deref() && parent_type.is_pointer() {
                let base_snapshot = self.expression_to_snapshot(lowerer, parent, true)?;
                let ty = parent.get_type();
                lowerer.pointer_address(ty, base_snapshot, place.position())
            } else {
                let base_address = self.pointer_deref_into_address(lowerer, parent)?;
                let position = place.position();
                match place {
                    vir_mid::Expression::Field(place) => lowerer.encode_field_address(
                        parent_type,
                        &place.field,
                        base_address,
                        position,
                    ),
                    vir_mid::Expression::Variant(place) => lowerer.encode_enum_variant_address(
                        parent_type,
                        &place.variant_index,
                        base_address,
                        position,
                    ),
                    _ => unreachable!("place: {place}"),
                }
            }
        } else {
            unreachable!("place: {place}");
        }
        // if let Some(deref_place) = place.get_last_dereferenced_pointer() {
        //     let base_snapshot = self.expression_to_snapshot(lowerer, deref_place, true)?;
        //     let ty = deref_place.get_type();
        //     lowerer.pointer_address(ty, base_snapshot, place.position())
        // } else {
        //     unreachable!("place: {place}");
        // }
    }

    fn acc_predicate_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        acc_predicate: &vir_mid::AccPredicate,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression>;

    // fn unfolding_to_snapshot(
    //     &mut self,
    //     lowerer: &mut Lowerer<'p, 'v, 'tcx>,
    //     unfolding: &vir_mid::Unfolding,
    //     expect_math_bool: bool,
    // ) -> SpannedEncodingResult<vir_low::Expression>;

    fn call_context(&self) -> CallContext;

    fn encode_lifetime_in_self_context(
        &self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        lifetime: vir_mid::ty::LifetimeConst,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let encoded_lifetime = match self.call_context() {
            CallContext::BuiltinMethod => {
                crate::encoder::middle::core_proof::snapshots::IntoPureSnapshot::to_pure_snapshot(
                    &lifetime, lowerer,
                )?
            }
            CallContext::Procedure => {
                lowerer.encode_lifetime_const_into_procedure_variable(lifetime)?
            }
        };
        Ok(encoded_lifetime.into())
    }

    fn unfolding_to_snapshot_with_body(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        predicate: &vir_mid::Predicate,
        body: vir_low::Expression,
        position: vir_low::Position,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        assert!(expect_math_bool, "not implemented");
        let predicate = match predicate {
            vir_mid::Predicate::OwnedNonAliased(predicate) => {
                let ty = predicate.place.get_type();
                lowerer.mark_owned_predicate_as_unfolded(ty)?;
                let place = lowerer.encode_expression_as_place(&predicate.place)?;
                let address = lowerer.encode_expression_as_place_address(&predicate.place)?;
                // let root_address = lowerer.extract_root_address(&predicate.place)?;
                // let snapshot =
                //     self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?;
                // predicate.place.to_procedure_snapshot(lowerer)?; // FIXME: This is probably wrong. It should take into account the current old.
                lowerer
                    .owned_non_aliased(self.call_context(), ty, ty, place, address, None, position)?
                    .unwrap_predicate_access_predicate()
            }
            _ => unimplemented!("{predicate}"),
        };
        let expression = vir_low::Expression::unfolding(predicate, body, position);
        Ok(expression)
    }

    fn unfolding_to_snapshot(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        unfolding: &vir_mid::Unfolding,
        expect_math_bool: bool,
    ) -> SpannedEncodingResult<vir_low::Expression> {
        let body = self.expression_to_snapshot(lowerer, &unfolding.body, expect_math_bool)?;
        self.unfolding_to_snapshot_with_body(
            lowerer,
            &unfolding.predicate,
            body,
            unfolding.position,
            expect_math_bool,
        )
        // let predicate = match &*unfolding.predicate {
        //     vir_mid::Predicate::OwnedNonAliased(predicate) => {
        //         let ty = predicate.place.get_type();
        //         lowerer.mark_owned_predicate_as_unfolded(ty)?;
        //         let place = lowerer.encode_expression_as_place(&predicate.place)?;
        //         let root_address = lowerer.extract_root_address(&predicate.place)?;
        //         let snapshot = self.expression_to_snapshot(lowerer, &predicate.place, expect_math_bool)?;
        //         // predicate.place.to_procedure_snapshot(lowerer)?; // FIXME: This is probably wrong. It should take into account the current old.
        //         lowerer
        //             .owned_non_aliased(
        //                 self.call_context(),
        //                 ty,
        //                 ty,
        //                 place,
        //                 root_address,
        //                 snapshot,
        //                 None,
        //             )?
        //             .unwrap_predicate_access_predicate()
        //     }
        //     _ => unimplemented!("{unfolding}"),
        // };
        // let body = self.expression_to_snapshot(lowerer, &unfolding.body, expect_math_bool)?;
        // let expression = vir_low::Expression::unfolding(predicate, body, unfolding.position);
        // Ok(expression)
    }

    fn eval_in_to_snapshot<F>(
        &mut self,
        _lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        _eval_in: &vir_mid::EvalIn,
        _expect_math_bool: bool,
        _body_to_snapshot: F,
    ) -> SpannedEncodingResult<vir_low::Expression>
    where
        F: FnOnce(
            &mut Self,
            &mut Lowerer<'p, 'v, 'tcx>,
            &vir_mid::Expression,
            bool,
        ) -> SpannedEncodingResult<vir_low::Expression>,
    {
        unimplemented!("FIXME: Make this abstract.");
    }

    fn owned_non_aliased_snap(
        &mut self,
        lowerer: &mut Lowerer<'p, 'v, 'tcx>,
        ty: &vir_mid::Type,
        pointer_place: &vir_mid::Expression,
    ) -> SpannedEncodingResult<vir_low::Expression>;

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
