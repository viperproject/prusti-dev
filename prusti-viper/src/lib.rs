#![feature(rustc_private)]

use rustc_hash::FxHashMap;
use viper::{self, AstFactory};

pub fn program_to_viper<'vir, 'v>(program: vir::Program<'vir>, ast: &'vir AstFactory<'v>) -> viper::Program<'vir> {
    let mut domains: FxHashMap<_, _> = Default::default();
    let mut domain_functions: FxHashMap<_, _> = Default::default();
    let mut domain_axioms: FxHashMap<_, _> = Default::default();
    for domain in program.domains {
        domains.insert(domain.name, *domain);
        for function in domain.functions {
            domain_functions.insert(function.name.to_str(), (*domain, *function));
        }
        for axiom in domain.axioms {
            domain_axioms.insert(axiom.name, (*domain, *axiom));
        }
    }
    let ctx = ToViperContext {
        ast,
        domains,
        domain_functions,
        domain_axioms,
    };
    program.to_viper(&ctx)
}

/// Context for conversion of VIR nodes to Viper AST. We need to keep track of
/// domain information in particular, since domain function application nodes
/// must be created with information that we do not store in the VIR.
pub struct ToViperContext<'vir, 'v> {
    /// Wrapper around JNI methods to create Viper AST methods.
    ast: &'v AstFactory<'v>,

    /// Map of all domains in the program, keyed by name.
    domains: FxHashMap<&'vir str, vir::Domain<'vir>>,

    /// Map of all domain functions in the program, keyed by name.
    domain_functions: FxHashMap<&'vir str, (vir::Domain<'vir>, vir::DomainFunction<'vir>)>,

    /// Map of all domain axioms in the program, keyed by name.
    domain_axioms: FxHashMap<&'vir str, (vir::Domain<'vir>, vir::DomainAxiom<'vir>)>,
}

/// Conversion of one VIR node into one Viper AST node.
pub trait ToViper<'vir, 'v> {
    /// Type of the created Viper AST node.
    type Output;

    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output;
}

/// Conversion of one VIR node into a vector of Viper AST nodes.
pub trait ToViperVec<'vir, 'v> {
    /// Type of a single created Viper AST node.
    type Output;

    /// Extend the given vector with the converted contents of `self`.
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>);

    /// Indicate how many elements there are in `self`. Does not need to be
    /// provided, nor does it need to be accurate; this is only used to set a
    /// capacity for vectors.
    fn size_hint(&self) -> Option<usize> {
        None
    }

    /// Helper method to allocate a vector and extend it with `self`.
    fn to_viper_vec(&self, ctx: &ToViperContext<'vir, 'v>) -> Vec<Self::Output> {
        let mut result = match self.size_hint() {
            Some(hint) => Vec::with_capacity(hint),
            None => Vec::new(),
        };
        self.to_viper_extend(&mut result, ctx);
        result
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::AccField<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.field_access_predicate(
            ctx.ast.field_access(
                self.recv.to_viper(ctx),
                self.field.to_viper(ctx),
                // TODO: position
            ),
            self.perm.map(|v| v.to_viper(ctx)).unwrap_or_else(|| ctx.ast.full_perm()),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::BinOp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        let lhs = self.lhs.to_viper(ctx);
        let rhs = self.rhs.to_viper(ctx);
        // TODO: position
        match self.kind {
            vir::BinOpKind::CmpEq => ctx.ast.eq_cmp(lhs, rhs),
            vir::BinOpKind::CmpNe => ctx.ast.ne_cmp(lhs, rhs),
            vir::BinOpKind::CmpGt => ctx.ast.gt_cmp(lhs, rhs),
            vir::BinOpKind::CmpLt => ctx.ast.lt_cmp(lhs, rhs),
            vir::BinOpKind::CmpGe => ctx.ast.ge_cmp(lhs, rhs),
            vir::BinOpKind::CmpLe => ctx.ast.le_cmp(lhs, rhs),
            vir::BinOpKind::And => ctx.ast.and(lhs, rhs),
            vir::BinOpKind::Or => ctx.ast.or(lhs, rhs),
            vir::BinOpKind::Add => ctx.ast.add(lhs, rhs),
            vir::BinOpKind::Sub => ctx.ast.sub(lhs, rhs),
            vir::BinOpKind::Mul => ctx.ast.mul(lhs, rhs),
            vir::BinOpKind::Div => ctx.ast.div(lhs, rhs),
            vir::BinOpKind::Mod => ctx.ast.mul(lhs, rhs),
            vir::BinOpKind::Implies => ctx.ast.implies(lhs, rhs),
        }
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::CfgBlock<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        Some(1 + self.stmts.len() + self.terminator.size_hint().unwrap_or(1))
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>) {
        vec.push(self.label.to_viper(ctx));
        vec.extend(self.stmts.iter().map(|v| v.to_viper(ctx)));
        self.terminator.to_viper_extend(vec, ctx);
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::CfgBlockLabel<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.label(
            &self.name(),
            &[], // TODO: invariants
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Const<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        // TODO: position
        match self {
            vir::ConstData::Bool(true) => ctx.ast.true_lit(),
            vir::ConstData::Bool(false) => ctx.ast.false_lit(),
            vir::ConstData::Int(v) if *v < (i64::MAX as u128) => ctx.ast.int_lit(*v as i64),
            vir::ConstData::Int(v) => ctx.ast.int_lit_from_ref(v),
            vir::ConstData::Wildcard => ctx.ast.wildcard_perm(),
            vir::ConstData::Null => ctx.ast.null_lit(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Domain<'vir> {
    type Output = viper::Domain<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.domain(
            self.name,
            &self.functions.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.axioms.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.typarams.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainAxiom<'vir> {
    type Output = viper::NamedDomainAxiom<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        let (domain, _) = ctx.domain_axioms.get(self.name).expect("no domain for domain axiom");
        ctx.ast.named_domain_axiom(
            self.name,
            self.expr.to_viper(ctx),
            domain.name,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainFunction<'vir> {
    type Output = viper::DomainFunc<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        let (domain, _) = ctx.domain_functions.get(self.name.to_str()).expect("no domain for domain function");
        ctx.ast.domain_func(
            self.name.to_str(),
            &self.args.iter().enumerate().map(|(idx, v)| ctx.ast.local_var_decl(
                &format!("arg{idx}"),
                v.to_viper(ctx),
            )).collect::<Vec<_>>(),
            self.ret.to_viper(ctx),
            self.unique,
            domain.name,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainParam<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.type_var(self.name)
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Expr<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        match self.kind {
            vir::ExprKindData::AccField(v) => v.to_viper(ctx),
            vir::ExprKindData::BinOp(v) => v.to_viper(ctx),
            vir::ExprKindData::Const(v) => v.to_viper(ctx),
            vir::ExprKindData::Field(recv, field) => ctx.ast.field_access(
                recv.to_viper(ctx),
                field.to_viper(ctx),
                // TODO: position
            ),
            vir::ExprKindData::Forall(v) => v.to_viper(ctx),
            vir::ExprKindData::FuncApp(v) => v.to_viper(ctx),
            vir::ExprKindData::Let(v) => v.to_viper(ctx),
            vir::ExprKindData::Local(v) => v.to_viper(ctx),
            vir::ExprKindData::Old(v) => ctx.ast.old(v.to_viper(ctx)), // TODO: position
            vir::ExprKindData::PredicateApp(v) => v.to_viper(ctx),
            vir::ExprKindData::Result(ty) => ctx.ast.result_with_pos(
                ty.to_viper(ctx),
                ctx.ast.no_position(), // TODO: position
            ),
            vir::ExprKindData::Ternary(v) => v.to_viper(ctx),
            vir::ExprKindData::Unfolding(v) => v.to_viper(ctx),
            vir::ExprKindData::UnOp(v) => v.to_viper(ctx),

            //vir::ExprKindData::Lazy(&'vir str, Box<dyn for <'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>),
            //vir::ExprKindData::Todo(&'vir str) => unreachable!(),

            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Field<'vir> {
    type Output = viper::Field<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.field(
            self.name,
            self.ty.to_viper(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Forall<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.forall(
            &self.qvars.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.triggers.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            self.body.to_viper(ctx),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::FuncApp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        if let Some((domain, _)) = ctx.domain_functions.get(self.target) {
            ctx.ast.domain_func_app2(
                self.target,
                &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
                &[],
                self.result_ty.to_viper(ctx),
                domain.name,
                ctx.ast.no_position(), // TODO: position
            )
        } else {
            ctx.ast.func_app(
                self.target,
                &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
                self.result_ty.to_viper(ctx),
                ctx.ast.no_position(), // TODO: position
            )
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Function<'vir> {
    type Output = viper::Function<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.function(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            self.ret.to_viper(ctx),
            &self.pres.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            ctx.ast.no_position(), // TODO: position
            self.expr.map(|v| v.to_viper(ctx)),
        )
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::GotoIf<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        if self.targets.is_empty() {
            Some(1 + self.otherwise_statements.len())
        } else {
            Some(1)
        }
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>) {
        if self.targets.is_empty() {
            self.otherwise_statements.iter()
                .for_each(|v| vec.push(v.to_viper(ctx)));
            vec.push(ctx.ast.goto(&self.otherwise.name()));
            return;
        }
        let value = self.value.to_viper(ctx);
        vec.push(self.targets.iter()
            .rfold({
                let mut vec_otherwise = Vec::with_capacity(1 + self.otherwise_statements.len());
                self.otherwise_statements.iter()
                    .for_each(|v| vec_otherwise.push(v.to_viper(ctx)));
                vec_otherwise.push(ctx.ast.goto(&self.otherwise.name()));
                ctx.ast.seqn(&vec_otherwise, &[])
            }, |else_, target| {
                let mut vec_then = Vec::with_capacity(1 + target.statements.len());
                target.statements.iter()
                    .for_each(|v| vec_then.push(v.to_viper(ctx)));
                vec_then.push(ctx.ast.goto(&target.label.name()));
                let stmt = ctx.ast.if_stmt(
                    ctx.ast.eq_cmp(
                        value,
                        target.value.to_viper(ctx),
                    ),
                    ctx.ast.seqn(&vec_then, &[]),
                    else_,
                );
                ctx.ast.seqn(&[stmt], &[])
            }))
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Let<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.let_expr(
            ctx.ast.local_var_decl(
                self.name,
                self.val.ty().to_viper(ctx),
            ),
            self.val.to_viper(ctx),
            self.expr.to_viper(ctx),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalData<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.local_var(
            self.name,
            self.ty.to_viper(ctx),
            // TODO: Use a real position here
            ctx.ast.no_position()
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalDeclData<'vir> {
    type Output = viper::LocalVarDecl<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.local_var_decl(
            self.name,
            self.ty.to_viper(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Method<'vir> {
    type Output = viper::Method<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.method(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.rets.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.pres.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            self.body.map(|body| {
                let size_hint = body.blocks.iter().flat_map(|b| b.size_hint()).sum();
                let mut result = if size_hint > 0 {
                    Vec::with_capacity(size_hint)
                } else {
                    Vec::new()
                };
                let mut declarations: Vec<viper::Declaration> = Vec::with_capacity(1 + body.blocks.len());
                body.blocks.iter()
                    .for_each(|b| {
                        declarations.push(ctx.ast.label(
                            &b.label.name(),
                            &[],
                        ).into());
                        b.stmts.iter()
                            .for_each(|s| match s {
                                vir::StmtGenData::LocalDecl(decl, _) => declarations.push(decl.to_viper(ctx).into()),
                                _ => (),
                            });
                        b.to_viper_extend(&mut result, ctx);
                    });
                ctx.ast.seqn(
                    &result,
                    &declarations,
                )
            }),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::MethodCall<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.method_call_with_pos(
            self.method,
            &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            &self.targets.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            ctx.ast.no_position(), // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PredicateApp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.predicate_access_predicate(
            ctx.ast.predicate_access(
                &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
                self.target
            ),
            self.perm.map(|v| v.to_viper(ctx)).unwrap_or_else(|| ctx.ast.full_perm()),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Predicate<'vir> {
    type Output = viper::Predicate<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.predicate(
            self.name,
            &self.args.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            self.expr.map(|v| v.to_viper(ctx)),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Program<'vir> {
    type Output = viper::Program<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.program(
            &self.domains.iter().map(|v| v.to_viper(&ctx)).collect::<Vec<_>>(),
            &self.fields.iter().map(|v| v.to_viper(&ctx)).collect::<Vec<_>>(),
            &self.functions.iter().map(|v| v.to_viper(&ctx)).collect::<Vec<_>>(),
            &self.predicates.iter().map(|v| v.to_viper(&ctx)).collect::<Vec<_>>(),
            &self.methods.iter().map(|v| v.to_viper(&ctx)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PureAssign<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.local_var_assign(
            // TODO: this won't work, maybe abstract assign?
            self.lhs.to_viper(ctx),
            self.rhs.to_viper(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Stmt<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        match self {
            vir::StmtGenData::Comment(v) => ctx.ast.comment(v),
            vir::StmtGenData::Exhale(v) => ctx.ast.exhale(
                v.to_viper(ctx),
                ctx.ast.no_position(), // TODO: position
            ),
            vir::StmtGenData::Fold(pred) => ctx.ast.fold(
                pred.to_viper(ctx),
                // TODO: position
            ),
            vir::StmtGenData::Inhale(v) => ctx.ast.inhale(
                v.to_viper(ctx),
                ctx.ast.no_position(), // TODO: position
            ),
            vir::StmtGenData::LocalDecl(decl, Some(expr)) => ctx.ast.local_var_assign(
                ctx.ast.local_var(
                    decl.name,
                    decl.ty.to_viper(ctx),
                    ctx.ast.no_position(),
                    // TODO: position
                ),
                expr.to_viper(ctx),
                // TODO: position
            ),
            vir::StmtGenData::LocalDecl(decl, None) => ctx.ast.comment(&format!("var {}", decl.name)),
            vir::StmtGenData::MethodCall(v) => v.to_viper(ctx),
            vir::StmtGenData::PureAssign(v) => v.to_viper(ctx),
            vir::StmtGenData::Unfold(pred) => ctx.ast.unfold(
                pred.to_viper(ctx),
                // TODO: position
            ),
            //vir::StmtGenData::Dummy(#[reify_copy] &'vir str),
            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::TerminatorStmt<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        if let vir::TerminatorStmtGenData::GotoIf(v) = self {
            v.size_hint()
        } else {
            Some(1)
        }
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>) {
        match self {
            vir::TerminatorStmtGenData::AssumeFalse => vec.push(ctx.ast.inhale(
                ctx.ast.false_lit(), // TODO: position
                ctx.ast.no_position(), // TODO: position
            )),
            vir::TerminatorStmtGenData::Goto(label) => vec.push(ctx.ast.goto(&label.name())),
            vir::TerminatorStmtGenData::GotoIf(v) => v.to_viper_extend(vec, ctx),
            vir::TerminatorStmtGenData::Exit => vec.push(ctx.ast.comment("return")),
            vir::TerminatorStmtGenData::Dummy(v) => vec.push(ctx.ast.seqn(
                &[
                    ctx.ast.comment(v),
                    ctx.ast.inhale(
                        ctx.ast.false_lit(), // TODO: position
                        ctx.ast.no_position(), // TODO: position
                    ),
                ],
                &[],
            )),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Ternary<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.cond_exp(
            self.cond.to_viper(ctx),
            self.then.to_viper(ctx),
            self.else_.to_viper(ctx),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Trigger<'vir> {
    type Output = viper::Trigger<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        ctx.ast.trigger(
            &self.exprs.iter().map(|v| v.to_viper(ctx)).collect::<Vec<_>>(),
            // TODO: position
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Type<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        match self {
            vir::TypeData::Int => ctx.ast.int_type(),
            vir::TypeData::Bool => ctx.ast.bool_type(),
            vir::TypeData::DomainTypeParam(param) => ctx.ast.type_var(param.name),
            vir::TypeData::Domain(name, params) => {
                let domain = ctx.domains.get(name).unwrap_or_else(|| panic!("Domain {name} not found"));
                ctx.ast.domain_type(
                    name,
                    &domain.typarams.iter()
                        .zip(params.iter())
                        .map(|(domain_param, actual)| (ctx.ast.type_var(domain_param.name), actual.to_viper(ctx)))
                        .collect::<Vec<_>>(),
                    &domain.typarams.iter()
                        .map(|v| ctx.ast.type_var(v.name))
                        .collect::<Vec<_>>(),
                )
            }
            vir::TypeData::Ref => ctx.ast.ref_type(),
            vir::TypeData::Perm => ctx.ast.perm_type(),
            //vir::TypeData::Predicate, // The type of a predicate application
            //vir::TypeData::Unsupported(UnsupportedType<'vir>)
            other => unimplemented!("{:?}", other),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::UnOp<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        let expr = self.expr.to_viper(ctx);
        // TODO: position
        match self.kind {
            vir::UnOpKind::Neg => ctx.ast.minus(expr),
            vir::UnOpKind::Not => ctx.ast.not(expr),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Unfolding<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        // TODO: position
        ctx.ast.unfolding(
            self.target.to_viper(ctx),
            self.expr.to_viper(ctx),
        )
    }
}
