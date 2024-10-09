#![feature(rustc_private)]

use rustc_hash::FxHashMap;
use viper::{self, AstFactory, Position};

/// Convert the given VIR program into a Viper program (i.e., Java object).
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
    program.to_viper_no_pos(&ctx)
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

impl<'vir, 'v> ToViperContext<'vir, 'v> {
    /// If a span is given, convert it to a Viper position. Otherwise, return
    /// a "no position".
    // TODO: This signature is chosen to accommodate optional spans in
    //   expressions and statements. When a span is *always* set,then this
    //   should be changed.
    fn span_to_pos(&self, span: Option<&'vir vir::VirSpan<'vir>>) -> Position {
        if let Some(span) = span {
            // TODO: virtual_position seems more appropriate (no need to store
            //   columns and lines which we don't use anyway), but it is not
            //   a HasIdentifier implementation; should be changed in silver
            // self.ast.virtual_position(format!("{}", span.id))
            self.ast.identifier_position(0, 0, format!("{}", span.id))
        } else {
            self.ast.no_position()
        }
    }
}

/// Conversion of one VIR node into one Viper AST node.
///
/// **About spans and positions**
/// Regarding the three conversion methods in this trait. The method that
/// should be implemented for all VIR types is `to_viper`, not the other two,
/// which are just convenience wrappers.
/// In many cases, the `pos` received in `to_viper` should be ignored: it only
/// exists for cases where `Self` should have a position, but it is stored in
/// the parent. For example, `ExprGenData` contains a span, but allocating
/// the Java object is dispatched to another type, such as `TernaryData`. The
/// latter does not contain its own span, so the span (converted to a position)
/// must be passed to the ternary through the `pos` argument.
pub trait ToViper<'vir, 'v> {
    /// Type of the created Viper AST node.
    type Output;

    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output;
}

/// Conversion of one VIR node into a vector of Viper AST nodes.
pub trait ToViperVec<'vir, 'v> {
    /// Type of a single created Viper AST node.
    type Output;

    /// Extend the given vector with the converted contents of `self`.
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>, pos: Position);

    /// Indicate how many elements there are in `self`. Does not need to be
    /// provided, nor does it need to be accurate; this is only used to set a
    /// capacity for vectors.
    fn size_hint(&self) -> Option<usize> {
        None
    }

    /// Helper method to allocate a vector and extend it with `self`.
    fn to_viper_vec(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Vec<Self::Output> {
        let mut result = match self.size_hint() {
            Some(hint) => Vec::with_capacity(hint),
            None => Vec::new(),
        };
        self.to_viper_extend(&mut result, ctx, pos);
        result
    }
}

trait ToViperPosHelper<'vir, 'v> {
    type Output;
    fn to_viper_no_pos(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output;
    fn to_viper_with_span(&self, ctx: &ToViperContext<'vir, 'v>, span: Option<&'vir vir::VirSpan<'vir>>) -> Self::Output;
}
impl<'vir, 'v, T: ToViper<'vir, 'v>> ToViperPosHelper<'vir, 'v> for T {
    type Output = <Self as ToViper<'vir, 'v>>::Output;
    fn to_viper_no_pos(&self, ctx: &ToViperContext<'vir, 'v>) -> Self::Output {
        self.to_viper(ctx, ctx.ast.no_position())
    }
    fn to_viper_with_span(&self, ctx: &ToViperContext<'vir, 'v>, span: Option<&'vir vir::VirSpan<'vir>>) -> Self::Output {
        self.to_viper(ctx, ctx.span_to_pos(span))
    }
}

trait ToViperVecPosHelper<'vir, 'v> {
    type Output;
    fn to_viper_extend_no_pos(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>);
    fn to_viper_vec_no_pos(&self, ctx: &ToViperContext<'vir, 'v>) -> Vec<Self::Output>;
}
impl<'vir, 'v, T: ToViperVec<'vir, 'v>> ToViperVecPosHelper<'vir, 'v> for T {
    type Output = <Self as ToViperVec<'vir, 'v>>::Output;
    fn to_viper_extend_no_pos(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>) {
        self.to_viper_extend(vec, ctx, ctx.ast.no_position());
    }
    fn to_viper_vec_no_pos(&self, ctx: &ToViperContext<'vir, 'v>) -> Vec<Self::Output> {
        self.to_viper_vec(ctx, ctx.ast.no_position())
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::AccField<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.field_access_predicate_with_pos(
            ctx.ast.field_access_with_pos(
                self.recv.to_viper_no_pos(ctx),
                self.field.to_viper_no_pos(ctx),
                pos,
            ),
            self.perm.map(|v| v.to_viper_no_pos(ctx)).unwrap_or_else(|| ctx.ast.full_perm()),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::BinOp<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        let lhs = self.lhs.to_viper_no_pos(ctx);
        let rhs = self.rhs.to_viper_no_pos(ctx);
        match self.kind {
            vir::BinOpKind::CmpEq => ctx.ast.eq_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::CmpNe => ctx.ast.ne_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::CmpGt => ctx.ast.gt_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::CmpLt => ctx.ast.lt_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::CmpGe => ctx.ast.ge_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::CmpLe => ctx.ast.le_cmp_with_pos(lhs, rhs, pos),
            vir::BinOpKind::And => ctx.ast.and_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Or => ctx.ast.or_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Add => ctx.ast.add_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Sub => ctx.ast.sub_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Mul => ctx.ast.mul_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Div => ctx.ast.div_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Mod => ctx.ast.mod_with_pos(lhs, rhs, pos),
            vir::BinOpKind::Implies => ctx.ast.implies_with_pos(lhs, rhs, pos),
        }
    }
}

impl<'vir, 'v> ToViperVec<'vir, 'v> for vir::CfgBlock<'vir> {
    type Output = viper::Stmt<'v>;
    fn size_hint(&self) -> Option<usize> {
        Some(1 + self.stmts.len() + self.terminator.size_hint().unwrap_or(1))
    }
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>, _pos: Position) {
        vec.push(self.label.to_viper_no_pos(ctx)); // TODO: pass own position to label?
        vec.extend(self.stmts.iter().map(|v| v.to_viper_no_pos(ctx)));
        self.terminator.to_viper_extend_no_pos(vec, ctx);
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::CfgBlockLabel<'vir> {
    type Output = viper::Stmt<'v>;
    // `pos` coming from the parent `Stmt` should be used, but the node
    //   created her cannot be created with a position
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.label(
            &self.name(),
            &[], // TODO: invariants
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Const<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        match self {
            vir::ConstData::Bool(true) => ctx.ast.true_lit_with_pos(pos),
            vir::ConstData::Bool(false) => ctx.ast.false_lit_with_pos(pos),
            vir::ConstData::Int(v) if *v < (i64::MAX as u128) => ctx.ast.int_lit_with_pos(*v as i64, pos),
            vir::ConstData::Int(v) => ctx.ast.int_lit_from_ref_with_pos(v, pos),
            vir::ConstData::Wildcard => ctx.ast.wildcard_perm(),
            vir::ConstData::Null => ctx.ast.null_lit_with_pos(pos),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Domain<'vir> {
    type Output = viper::Domain<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.domain(
            self.name,
            &self.functions.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.axioms.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.typarams.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainAxiom<'vir> {
    type Output = viper::NamedDomainAxiom<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        let (domain, _) = ctx.domain_axioms.get(self.name).expect("no domain for domain axiom");
        ctx.ast.named_domain_axiom(
            self.name,
            self.expr.to_viper_no_pos(ctx),
            domain.name,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainFunction<'vir> {
    type Output = viper::DomainFunc<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        let (domain, _) = ctx.domain_functions.get(self.name.to_str()).expect("no domain for domain function");
        ctx.ast.domain_func(
            self.name.to_str(),
            &self.args.iter().enumerate().map(|(idx, v)| ctx.ast.local_var_decl(
                &format!("arg{idx}"),
                v.to_viper_no_pos(ctx),
            )).collect::<Vec<_>>(),
            self.ret.to_viper_no_pos(ctx),
            self.unique,
            domain.name,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::DomainParam<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.type_var(self.name)
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Expr<'vir> {
    type Output = viper::Expr<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        match self.kind {
            vir::ExprKindData::AccField(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::BinOp(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Const(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Field(recv, field) => ctx.ast.field_access_with_pos(
                recv.to_viper_no_pos(ctx),
                field.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
            ),
            vir::ExprKindData::Forall(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::FuncApp(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Let(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Local(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Old(v) => ctx.ast.old(v.to_viper_no_pos(ctx)), // TODO: position
            vir::ExprKindData::PredicateApp(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Result(ty) => ctx.ast.result_with_pos(
                ty.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
            ),
            vir::ExprKindData::Ternary(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::Unfolding(v) => v.to_viper_with_span(ctx, self.span),
            vir::ExprKindData::UnOp(v) => v.to_viper_with_span(ctx, self.span),

            //vir::ExprKindData::Lazy(&'vir str, Box<dyn for <'a> Fn(&'vir crate::VirCtxt<'a>, Curr) -> Next + 'vir>),
            //vir::ExprKindData::Todo(&'vir str) => unreachable!(),

            _ => unimplemented!(),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Field<'vir> {
    type Output = viper::Field<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.field(
            self.name,
            self.ty.to_viper_no_pos(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Forall<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.forall_with_pos(
            &self.qvars.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.triggers.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            self.body.to_viper_no_pos(ctx),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::FuncApp<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        if let Some((domain, _)) = ctx.domain_functions.get(self.target) {
            ctx.ast.domain_func_app2(
                self.target,
                &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
                &[],
                self.result_ty.to_viper_no_pos(ctx),
                domain.name,
                pos,
            )
        } else {
            ctx.ast.func_app(
                self.target,
                &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
                self.result_ty.to_viper_no_pos(ctx),
                pos,
            )
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Function<'vir> {
    type Output = viper::Function<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.function(
            self.name,
            &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            self.ret.to_viper_no_pos(ctx),
            &self.pres.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            ctx.ast.no_position(), // TODO: position (each function should have its own)
            self.expr.map(|v| v.to_viper_no_pos(ctx)),
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
    // `pos` coming from the parent `Stmt` should be used, but the nodes
    //   created her cannot be created with positions
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>, _pos: Position) {
        if self.targets.is_empty() {
            self.otherwise_statements.iter()
                .for_each(|v| vec.push(v.to_viper_no_pos(ctx)));
            vec.push(ctx.ast.goto(&self.otherwise.name()));
            return;
        }
        let value = self.value.to_viper_no_pos(ctx);
        vec.push(self.targets.iter()
            .rfold({
                let mut vec_otherwise = Vec::with_capacity(1 + self.otherwise_statements.len());
                self.otherwise_statements.iter()
                    .for_each(|v| vec_otherwise.push(v.to_viper_no_pos(ctx)));
                vec_otherwise.push(ctx.ast.goto(&self.otherwise.name()));
                ctx.ast.seqn(&vec_otherwise, &[])
            }, |else_, target| {
                let mut vec_then = Vec::with_capacity(1 + target.statements.len());
                target.statements.iter()
                    .for_each(|v| vec_then.push(v.to_viper_no_pos(ctx)));
                vec_then.push(ctx.ast.goto(&target.label.name()));
                let stmt = ctx.ast.if_stmt(
                    ctx.ast.eq_cmp(
                        value,
                        target.value.to_viper_no_pos(ctx),
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
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.let_expr_with_pos(
            ctx.ast.local_var_decl(
                self.name,
                self.val.ty().to_viper_no_pos(ctx),
            ),
            self.val.to_viper_no_pos(ctx),
            self.expr.to_viper_no_pos(ctx),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalData<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.local_var(
            self.name,
            self.ty.to_viper_no_pos(ctx),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::LocalDeclData<'vir> {
    type Output = viper::LocalVarDecl<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.local_var_decl(
            self.name,
            self.ty.to_viper_no_pos(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Method<'vir> {
    type Output = viper::Method<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.method(
            self.name,
            &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.rets.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.pres.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.posts.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
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
                            .for_each(|s| match s.kind {
                                vir::StmtKindGenData::LocalDecl(decl, _) => declarations.push(decl.to_viper_no_pos(ctx).into()),
                                _ => (),
                            });
                        b.to_viper_extend_no_pos(&mut result, ctx);
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
    // `pos` coming from the parent `Stmt` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.method_call_with_pos(
            self.method,
            &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            &self.targets.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PredicateApp<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.predicate_access_predicate_with_pos(
            ctx.ast.predicate_access_with_pos(
                &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
                self.target,
                pos,
            ),
            self.perm.map(|v| v.to_viper_no_pos(ctx)).unwrap_or_else(|| ctx.ast.full_perm()),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Predicate<'vir> {
    type Output = viper::Predicate<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.predicate(
            self.name,
            &self.args.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            self.expr.map(|v| v.to_viper_no_pos(ctx)),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Program<'vir> {
    type Output = viper::Program<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.program(
            &self.domains.iter().map(|v| v.to_viper_no_pos(&ctx)).collect::<Vec<_>>(),
            &self.fields.iter().map(|v| v.to_viper_no_pos(&ctx)).collect::<Vec<_>>(),
            &self.functions.iter().map(|v| v.to_viper_no_pos(&ctx)).collect::<Vec<_>>(),
            &self.predicates.iter().map(|v| v.to_viper_no_pos(&ctx)).collect::<Vec<_>>(),
            &self.methods.iter().map(|v| v.to_viper_no_pos(&ctx)).collect::<Vec<_>>(),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::PureAssign<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.local_var_assign(
            // TODO: this won't work, maybe abstract assign?
            self.lhs.to_viper_no_pos(ctx),
            self.rhs.to_viper_no_pos(ctx),
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Stmt<'vir> {
    type Output = viper::Stmt<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        match self.kind {
            vir::StmtKindGenData::Comment(v) => ctx.ast.comment(v),
            vir::StmtKindGenData::Exhale(v) => ctx.ast.exhale(
                v.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
            ),
            vir::StmtKindGenData::Fold(pred) => ctx.ast.fold_with_pos(
                pred.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
            ),
            vir::StmtKindGenData::Inhale(v) => ctx.ast.inhale(
                v.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
            ),
            vir::StmtKindGenData::LocalDecl(decl, Some(expr)) => ctx.ast.local_var_assign(
                ctx.ast.local_var_with_pos(
                    decl.name,
                    decl.ty.to_viper_no_pos(ctx),
                    ctx.span_to_pos(self.span),
                ),
                expr.to_viper_no_pos(ctx),
                // TODO: position?
            ),
            vir::StmtKindGenData::LocalDecl(decl, None) => ctx.ast.comment(&format!("var {}", decl.name)),
            vir::StmtKindGenData::MethodCall(v) => v.to_viper_with_span(ctx, self.span),
            vir::StmtKindGenData::PureAssign(v) => v.to_viper_with_span(ctx, self.span),
            vir::StmtKindGenData::Unfold(pred) => ctx.ast.unfold_with_pos(
                pred.to_viper_no_pos(ctx),
                ctx.span_to_pos(self.span),
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
    // `pos` coming from the parent `TerminatorStmt` is used
    fn to_viper_extend(&self, vec: &mut Vec<Self::Output>, ctx: &ToViperContext<'vir, 'v>, pos: Position) {
        match self {
            vir::TerminatorStmtGenData::AssumeFalse => vec.push(ctx.ast.inhale(
                ctx.ast.false_lit_with_pos(pos),
                pos,
            )),
            vir::TerminatorStmtGenData::Goto(label) => vec.push(ctx.ast.goto(&label.name())),
            vir::TerminatorStmtGenData::GotoIf(v) => v.to_viper_extend_no_pos(vec, ctx),
            vir::TerminatorStmtGenData::Exit => vec.push(ctx.ast.comment("return")),
            vir::TerminatorStmtGenData::Dummy(v) => vec.push(ctx.ast.seqn(
                &[
                    ctx.ast.comment(v),
                    ctx.ast.assert(
                        ctx.ast.false_lit_with_pos(pos),
                        pos,
                    ),
                ],
                &[],
            )),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Ternary<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.cond_exp_with_pos(
            self.cond.to_viper_no_pos(ctx),
            self.then.to_viper_no_pos(ctx),
            self.else_.to_viper_no_pos(ctx),
            pos,
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Trigger<'vir> {
    type Output = viper::Trigger<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
        ctx.ast.trigger(
            &self.exprs.iter().map(|v| v.to_viper_no_pos(ctx)).collect::<Vec<_>>(),
            // TODO: position (each trigger should have its own)
        )
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Type<'vir> {
    type Output = viper::Type<'v>;
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, _pos: Position) -> Self::Output {
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
                        .map(|(domain_param, actual)| (ctx.ast.type_var(domain_param.name), actual.to_viper_no_pos(ctx)))
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
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        let expr = self.expr.to_viper_no_pos(ctx);
        match self.kind {
            vir::UnOpKind::Neg => ctx.ast.minus_with_pos(expr, pos),
            vir::UnOpKind::Not => ctx.ast.not_with_pos(expr, pos),
        }
    }
}

impl<'vir, 'v> ToViper<'vir, 'v> for vir::Unfolding<'vir> {
    type Output = viper::Expr<'v>;
    // `pos` coming from the parent `Expr` is used
    fn to_viper(&self, ctx: &ToViperContext<'vir, 'v>, pos: Position) -> Self::Output {
        ctx.ast.unfolding_with_pos(
            self.target.to_viper_no_pos(ctx),
            self.expr.to_viper_no_pos(ctx),
            pos,
        )
    }
}
