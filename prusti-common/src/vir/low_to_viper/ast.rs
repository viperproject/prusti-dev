use super::{Context, ToViper, ToViperDecl};
use prusti_utils::force_matches;
use viper::{self, AstFactory};
use vir::low::{
    ast::{
        expression::{self, Expression},
        function::FunctionDecl,
        position::Position,
        predicate::PredicateDecl,
        statement::{self, Statement},
        ty::{BitVector, BitVectorSize, Float, Map, Type},
        variable::VariableDecl,
    },
    ty::Seq,
};

impl<'a, 'v> ToViper<'v, viper::Predicate<'v>> for &'a PredicateDecl {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &self.parameters.to_viper_decl(context, ast),
            self.body.as_ref().map(|body| body.to_viper(context, ast)),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Function<'v>> for &'a FunctionDecl {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Function<'v> {
        ast.function(
            &self.name,
            &self.parameters.to_viper_decl(context, ast),
            self.return_type.to_viper(context, ast),
            &self.pres.to_viper(context, ast),
            &self.posts.to_viper(context, ast),
            ast.no_position(),
            self.body.as_ref().map(|body| body.to_viper(context, ast)),
        )
    }
}

impl<'v> ToViper<'v, Vec<viper::Stmt<'v>>> for Vec<Statement> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Stmt<'v>> {
        self.iter()
            .map(|statement| statement.to_viper(context, ast))
            .collect()
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Statement {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Statement::Comment(statement) => statement.to_viper(context, ast),
            Statement::LogEvent(statement) => statement.to_viper(context, ast),
            Statement::Assume(statement) => statement.to_viper(context, ast),
            Statement::Assert(statement) => statement.to_viper(context, ast),
            Statement::Inhale(statement) => statement.to_viper(context, ast),
            Statement::Exhale(statement) => statement.to_viper(context, ast),
            Statement::Fold(statement) => statement.to_viper(context, ast),
            Statement::Unfold(statement) => statement.to_viper(context, ast),
            Statement::ApplyMagicWand(statement) => statement.to_viper(context, ast),
            Statement::Conditional(statement) => statement.to_viper(context, ast),
            Statement::MethodCall(statement) => statement.to_viper(context, ast),
            Statement::Assign(statement) => statement.to_viper(context, ast),
        }
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Comment {
    fn to_viper(&self, _context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.comment(&self.comment)
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::LogEvent {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            self.expression.is_domain_func_app(),
            "The log event has to be a domain function application: {}",
            self
        );
        ast.inhale(self.expression.to_viper(context, ast), ast.no_position())
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Assume {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.inhale(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Assert {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.assert(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Inhale {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.inhale(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Exhale {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.exhale(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Fold {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.fold_with_pos(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Unfold {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.unfold_with_pos(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::ApplyMagicWand {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.apply(
            self.expression.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Conditional {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.if_stmt(
            self.guard.to_viper(context, ast),
            ast.seqn(&self.then_branch.to_viper(context, ast), &[]),
            ast.seqn(&self.else_branch.to_viper(context, ast), &[]),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::MethodCall {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        assert!(
            !self.position.is_default(),
            "Statement with default position: {}",
            self
        );
        ast.method_call_with_pos(
            &self.method_name,
            &self.arguments.to_viper(context, ast),
            &self.targets.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Assign {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        let target_expression = Expression::local(self.target.clone(), self.position);
        ast.abstract_assign(
            target_expression.to_viper(context, ast),
            self.value.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, Vec<viper::Expr<'v>>> for Vec<Expression> {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.iter()
            .map(|expression| expression.to_viper(context, ast))
            .collect()
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expression {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let expression = match self {
            Expression::Local(expression) => expression.to_viper(context, ast),
            // Expression::Field(expression) => expression.to_viper(context, ast),
            Expression::LabelledOld(expression) => expression.to_viper(context, ast),
            Expression::Constant(expression) => expression.to_viper(context, ast),
            Expression::MagicWand(expression) => expression.to_viper(context, ast),
            Expression::PredicateAccessPredicate(expression) => expression.to_viper(context, ast),
            // Expression::FieldAccessPredicate(expression) => expression.to_viper(context, ast),
            // Expression::Unfolding(expression) => expression.to_viper(context, ast),
            Expression::UnaryOp(expression) => expression.to_viper(context, ast),
            Expression::BinaryOp(expression) => expression.to_viper(context, ast),
            Expression::PermBinaryOp(expression) => expression.to_viper(context, ast),
            Expression::ContainerOp(expression) => expression.to_viper(context, ast),
            Expression::Seq(expression) => expression.to_viper(context, ast),
            Expression::Conditional(expression) => expression.to_viper(context, ast),
            Expression::Quantifier(expression) => expression.to_viper(context, ast),
            // Expression::LetExpr(expression) => expression.to_viper(context, ast),
            Expression::FuncApp(expression) => expression.to_viper(context, ast),
            Expression::DomainFuncApp(expression) => expression.to_viper(context, ast),
            // Expression::InhaleExhale(expression) => expression.to_viper(context, ast),
            Expression::MapOp(expression) => expression.to_viper(context, ast),
            x => unimplemented!("{:?}", x),
        };
        if crate::config::simplify_encoding() {
            ast.simplified_expression(expression)
        } else {
            expression
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Local {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.variable.name == "__result" {
            ast.result_with_pos(
                self.variable.ty.to_viper(context, ast),
                self.position.to_viper(context, ast),
            )
        } else {
            ast.local_var_with_pos(
                &self.variable.name,
                self.variable.ty.to_viper(context, ast),
                self.position.to_viper(context, ast),
            )
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::LabelledOld {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if let Some(label) = &self.label {
            ast.labelled_old_with_pos(
                self.base.to_viper(context, ast),
                label,
                self.position.to_viper(context, ast),
            )
        } else {
            ast.old(self.base.to_viper(context, ast))
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Constant {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match &self.ty {
            Type::Int => match &self.value {
                expression::ConstantValue::Bool(_) => {
                    unreachable!()
                }
                expression::ConstantValue::Int(value) => {
                    ast.int_lit_with_pos(*value, self.position.to_viper(context, ast))
                }
                expression::ConstantValue::BigInt(value) => {
                    ast.int_lit_from_ref_with_pos(value, self.position.to_viper(context, ast))
                }
            },
            Type::Bool => match &self.value {
                expression::ConstantValue::Bool(true) => {
                    ast.true_lit_with_pos(self.position.to_viper(context, ast))
                }
                expression::ConstantValue::Bool(false) => {
                    ast.false_lit_with_pos(self.position.to_viper(context, ast))
                }
                _ => unreachable!(),
            },
            Type::Float(_) => unimplemented!(),
            Type::BitVector(_) => unimplemented!(),
            Type::Seq(_) => unimplemented!(),
            Type::Map(_) => unimplemented!(),
            Type::Ref => unimplemented!(),
            Type::Perm => match &self.value {
                expression::ConstantValue::Bool(_) => {
                    unreachable!()
                }
                expression::ConstantValue::Int(value) => match value {
                    0 => ast.no_perm(),
                    1 => ast.full_perm(),
                    -1 => ast.wildcard_perm(),
                    _ => unimplemented!("value: {}", value),
                },
                expression::ConstantValue::BigInt(_) => {
                    unimplemented!()
                }
            },
            Type::Domain(domain) => unimplemented!("domain: {:?} constant: {:?}", domain, self),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::MagicWand {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.magic_wand_with_pos(
            self.left.to_viper(context, ast),
            self.right.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::PredicateAccessPredicate {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let location = ast.predicate_access(&self.arguments.to_viper(context, ast), &self.name);
        if context.inside_trigger {
            location
        } else {
            ast.predicate_access_predicate_with_pos(
                location,
                self.permission.to_viper(context, ast),
                self.position.to_viper(context, ast),
            )
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::UnaryOp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self.op_kind {
            expression::UnaryOpKind::Minus => ast.minus_with_pos(
                self.argument.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::UnaryOpKind::Not => ast.not_with_pos(
                self.argument.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::BinaryOp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self.op_kind {
            expression::BinaryOpKind::EqCmp => ast.eq_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::NeCmp => ast.ne_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::GtCmp => ast.gt_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::GeCmp => ast.ge_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::LtCmp => ast.lt_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::LeCmp => ast.le_cmp_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Add => ast.add_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Sub => ast.sub_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Mul => ast.mul_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Div => ast.div_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Mod => ast.module_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::And => ast.and_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Or => ast.or_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
            expression::BinaryOpKind::Implies => ast.implies_with_pos(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
                self.position.to_viper(context, ast),
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::PermBinaryOp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self.op_kind {
            expression::PermBinaryOpKind::Add => ast.perm_add(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
            ),
            expression::PermBinaryOpKind::Sub => ast.perm_sub(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
            ),
            expression::PermBinaryOpKind::Mul => ast.perm_mul(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
            ),
            expression::PermBinaryOpKind::Div => ast.perm_div(
                self.left.to_viper(context, ast),
                self.right.to_viper(context, ast),
            ),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Conditional {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.cond_exp_with_pos(
            self.guard.to_viper(context, ast),
            self.then_expr.to_viper(context, ast),
            self.else_expr.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Quantifier {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let variables = self.variables.to_viper_decl(context, ast);
        let triggers = self
            .triggers
            .iter()
            .map(|trigger| (trigger, self.position).to_viper(context, ast))
            .collect::<Vec<_>>();
        let body = self.body.to_viper(context, ast);
        let pos = self.position.to_viper(context, ast);
        match self.kind {
            expression::QuantifierKind::ForAll => {
                ast.forall_with_pos(&variables[..], &triggers, body, pos)
            }
            expression::QuantifierKind::Exists => {
                ast.exists_with_pos(&variables[..], &triggers, body, pos)
            }
        }
    }
}

impl<'v, 'a> ToViper<'v, viper::Trigger<'v>> for (&'a expression::Trigger, Position) {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Trigger<'v> {
        let trigger_context = context.set_inside_trigger();
        ast.trigger_with_pos(
            &self.0.terms.to_viper(trigger_context, ast)[..],
            self.1.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::FuncApp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.func_app(
            &self.function_name,
            &self.arguments.to_viper(context, ast),
            self.return_type.to_viper(context, ast),
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::DomainFuncApp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.domain_func_app2(
            &self.function_name,
            &self.arguments.to_viper(context, ast),
            &[],
            self.return_type.to_viper(context, ast),
            &self.domain_name,
            self.position.to_viper(context, ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Seq {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let elems = self
            .elements
            .iter()
            .map(|e| e.to_viper(context, ast))
            .collect::<Vec<_>>();
        if elems.is_empty() {
            let elem_ty = force_matches!(&self.ty, Type::Seq(Seq { element_type }) => element_type);
            ast.empty_seq(elem_ty.to_viper(context, ast))
        } else {
            ast.explicit_seq(&elems)
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::ContainerOp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let left = || self.left.to_viper(context, ast);
        let right = || self.right.to_viper(context, ast);
        match self.op_kind {
            expression::ContainerOpKind::SeqConcat => ast.seq_append(left(), right()),
            expression::ContainerOpKind::SeqIndex => ast.seq_index(left(), right()),
            expression::ContainerOpKind::SeqLen => ast.seq_length(left()),
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::MapOp {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let (key_ty, val_ty) = match &self.map_ty {
            Type::Map(Map { key_type, val_type }) => (key_type, val_type),
            _ => unreachable!(),
        };
        let key_ty = key_ty.to_viper(context, ast);
        let val_ty = val_ty.to_viper(context, ast);

        let arg = |idx| (&self.operands[idx] as &Expression).to_viper(context, ast);

        match self.kind {
            expression::MapOpKind::Empty => ast.empty_map(key_ty, val_ty),
            expression::MapOpKind::Update => ast.update_map(arg(0), arg(1), arg(2)),
            expression::MapOpKind::Contains => ast.map_contains(arg(0), arg(1)),
            expression::MapOpKind::Lookup => ast.lookup_map(arg(0), arg(1)),
            expression::MapOpKind::Len => ast.map_len(arg(0)),
        }
    }
}

impl<'v> ToViper<'v, viper::Position<'v>> for Position {
    fn to_viper(&self, _context: Context, ast: &AstFactory<'v>) -> viper::Position<'v> {
        ast.identifier_position(self.line, self.column, self.id.to_string())
    }
}

impl<'v> ToViper<'v, viper::Type<'v>> for Type {
    fn to_viper(&self, context: Context, ast: &AstFactory<'v>) -> viper::Type<'v> {
        match self {
            Type::Int => ast.int_type(),
            Type::Bool => ast.bool_type(),
            Type::Ref => ast.ref_type(),
            Type::Perm => ast.perm_type(),
            Type::Domain(ty) => ast.domain_type(&ty.name, &[], &[]),
            Type::Seq(ty) => ast.seq_type(ty.element_type.to_viper(context, ast)),
            Type::Map(ty) => ast.map_type(
                ty.key_type.to_viper(context, ast),
                ty.val_type.to_viper(context, ast),
            ),
            Type::Float(Float::F32) => ast.backend_f32_type(),
            Type::Float(Float::F64) => ast.backend_f64_type(),
            Type::BitVector(bv_size) => match bv_size {
                BitVector::Signed(BitVectorSize::BV8) | BitVector::Unsigned(BitVectorSize::BV8) => {
                    ast.backend_bv8_type()
                }
                BitVector::Signed(BitVectorSize::BV16)
                | BitVector::Unsigned(BitVectorSize::BV16) => ast.backend_bv16_type(),
                BitVector::Signed(BitVectorSize::BV32)
                | BitVector::Unsigned(BitVectorSize::BV32) => ast.backend_bv32_type(),
                BitVector::Signed(BitVectorSize::BV64)
                | BitVector::Unsigned(BitVectorSize::BV64) => ast.backend_bv64_type(),
                BitVector::Signed(BitVectorSize::BV128)
                | BitVector::Unsigned(BitVectorSize::BV128) => ast.backend_bv128_type(),
            },
        }
    }
}

impl<'v> ToViperDecl<'v, Vec<viper::LocalVarDecl<'v>>> for Vec<VariableDecl> {
    fn to_viper_decl(
        &self,
        context: Context,
        ast: &AstFactory<'v>,
    ) -> Vec<viper::LocalVarDecl<'v>> {
        self.iter()
            .map(|variable| variable.to_viper_decl(context, ast))
            .collect()
    }
}

impl<'v> ToViperDecl<'v, viper::LocalVarDecl<'v>> for VariableDecl {
    fn to_viper_decl(&self, context: Context, ast: &AstFactory<'v>) -> viper::LocalVarDecl<'v> {
        ast.local_var_decl(&self.name, self.ty.to_viper(context, ast))
    }
}
