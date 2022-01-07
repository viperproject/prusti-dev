use super::{ToViper, ToViperDecl};
use viper::{self, AstFactory};
use vir::{
    legacy::RETURN_LABEL,
    low::ast::{
        expression::{self, Expression},
        function::FunctionDecl,
        position::Position,
        predicate::PredicateDecl,
        statement::{self, Statement},
        ty::{BitVector, Float, Type},
        variable::VariableDecl,
        PermAmount,
    },
};

impl<'a, 'v> ToViper<'v, viper::Predicate<'v>> for &'a PredicateDecl {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Predicate<'v> {
        ast.predicate(
            &self.name,
            &self.parameters.to_viper_decl(ast),
            self.body.as_ref().map(|body| body.to_viper(ast)),
        )
    }
}

impl<'a, 'v> ToViper<'v, viper::Function<'v>> for &'a FunctionDecl {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Function<'v> {
        ast.function(
            &self.name,
            &self.parameters.to_viper_decl(ast),
            self.return_type.to_viper(ast),
            &self.pres.to_viper(ast),
            &self.posts.to_viper(ast),
            ast.no_position(),
            self.body.as_ref().map(|body| body.to_viper(ast)),
        )
    }
}

impl<'v> ToViper<'v, Vec<viper::Stmt<'v>>> for Vec<Statement> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Stmt<'v>> {
        self.iter()
            .map(|statement| statement.to_viper(ast))
            .collect()
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for Statement {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        match self {
            Statement::Comment(statement) => statement.to_viper(ast),
            Statement::Inhale(statement) => statement.to_viper(ast),
            Statement::Exhale(statement) => statement.to_viper(ast),
            Statement::MethodCall(statement) => statement.to_viper(ast),
        }
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Comment {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.comment(&self.comment)
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Inhale {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        // FIXME: assert!(!pos.is_default(), "stmt with default pos: {}", self);
        ast.inhale(self.expression.to_viper(ast), self.position.to_viper(ast))
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::Exhale {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        // FIXME: assert!(!pos.is_default(), "stmt with default pos: {}", self);
        ast.exhale(self.expression.to_viper(ast), self.position.to_viper(ast))
    }
}

impl<'v> ToViper<'v, viper::Stmt<'v>> for statement::MethodCall {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Stmt<'v> {
        ast.method_call(
            &self.method_name,
            &self.arguments.to_viper(ast),
            &self.targets.to_viper(ast),
        )
    }
}
impl<'v> ToViper<'v, Vec<viper::Expr<'v>>> for Vec<Expression> {
    fn to_viper(&self, ast: &AstFactory<'v>) -> Vec<viper::Expr<'v>> {
        self.iter()
            .map(|expression| expression.to_viper(ast))
            .collect()
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for Expression {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        let expression = match self {
            Expression::Local(expression) => expression.to_viper(ast),
            Expression::Constant(expression) => expression.to_viper(ast),
            Expression::PredicateAccessPredicate(expression) => expression.to_viper(ast),
            Expression::FuncApp(expression) => expression.to_viper(ast),
            Expression::DomainFuncApp(expression) => expression.to_viper(ast),
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
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        if self.variable.name == "__result" {
            ast.result_with_pos(self.variable.ty.to_viper(ast), self.position.to_viper(ast))
        } else {
            ast.local_var_with_pos(
                &self.variable.name,
                self.variable.ty.to_viper(ast),
                self.position.to_viper(ast),
            )
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::Constant {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match &self.value {
            expression::ConstantValue::Bool(true) => {
                ast.true_lit_with_pos(self.position.to_viper(ast))
            }
            expression::ConstantValue::Bool(false) => {
                ast.false_lit_with_pos(self.position.to_viper(ast))
            }
            expression::ConstantValue::Int(value) => {
                ast.int_lit_with_pos(*value, self.position.to_viper(ast))
            }
            expression::ConstantValue::BigInt(value) => {
                ast.int_lit_from_ref_with_pos(value, self.position.to_viper(ast))
            }
            expression::ConstantValue::Float(expression::FloatConst::F32(value)) => {
                ast.backend_f32_lit(*value)
            }
            expression::ConstantValue::Float(expression::FloatConst::F64(value)) => {
                ast.backend_f64_lit(*value)
            }
            expression::ConstantValue::BitVector(bv_constant) => match bv_constant {
                expression::BitVectorConst::BV8(value) => ast.backend_bv8_lit(*value),
                expression::BitVectorConst::BV16(value) => ast.backend_bv16_lit(*value),
                expression::BitVectorConst::BV32(value) => ast.backend_bv32_lit(*value),
                expression::BitVectorConst::BV64(value) => ast.backend_bv64_lit(*value),
                expression::BitVectorConst::BV128(value) => ast.backend_bv128_lit(*value),
            },
        }
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::PredicateAccessPredicate {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.predicate_access_predicate_with_pos(
            ast.predicate_access(&self.arguments.to_viper(ast), &self.name),
            self.permission.to_viper(ast),
            self.position.to_viper(ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::FuncApp {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.func_app(
            &self.function_name,
            &self.arguments.to_viper(ast),
            self.return_type.to_viper(ast),
            self.position.to_viper(ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for expression::DomainFuncApp {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        ast.domain_func_app2(
            &self.function_name,
            &self.arguments.to_viper(ast),
            &[],
            self.return_type.to_viper(ast),
            &self.domain_name,
            self.position.to_viper(ast),
        )
    }
}

impl<'v> ToViper<'v, viper::Expr<'v>> for PermAmount {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Expr<'v> {
        match self {
            PermAmount::Write => ast.full_perm(),
            PermAmount::Read => unimplemented!(),
            PermAmount::Remaining => unimplemented!(),
        }
    }
}

impl<'v> ToViper<'v, viper::Position<'v>> for Position {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Position<'v> {
        ast.identifier_position(self.line, self.column, self.id.to_string())
    }
}

impl<'v> ToViper<'v, viper::Type<'v>> for Type {
    fn to_viper(&self, ast: &AstFactory<'v>) -> viper::Type<'v> {
        match self {
            Type::Int => ast.int_type(),
            Type::Bool => ast.bool_type(),
            Type::Ref => ast.ref_type(),
            Type::Domain(ty) => ast.domain_type(&ty.name, &[], &[]),
            Type::Seq(ty) => ast.seq_type(ty.element_type.to_viper(ast)),
            Type::Float(Float::F32) => ast.backend_f32_type(),
            Type::Float(Float::F64) => ast.backend_f64_type(),
            Type::BitVector(bv_size) => match bv_size {
                BitVector::BV8 => ast.backend_bv8_type(),
                BitVector::BV16 => ast.backend_bv16_type(),
                BitVector::BV32 => ast.backend_bv32_type(),
                BitVector::BV64 => ast.backend_bv64_type(),
                BitVector::BV128 => ast.backend_bv128_type(),
            },
        }
    }
}

impl<'v> ToViperDecl<'v, Vec<viper::LocalVarDecl<'v>>> for Vec<VariableDecl> {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> Vec<viper::LocalVarDecl<'v>> {
        self.iter()
            .map(|variable| variable.to_viper_decl(ast))
            .collect()
    }
}

impl<'v> ToViperDecl<'v, viper::LocalVarDecl<'v>> for VariableDecl {
    fn to_viper_decl(&self, ast: &AstFactory<'v>) -> viper::LocalVarDecl<'v> {
        ast.local_var_decl(&self.name, self.ty.to_viper(ast))
    }
}
