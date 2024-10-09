use cfg_if::cfg_if;
use std::fmt::Debug;
use prusti_rustc_interface::middle::ty;
use crate::{
    callable_idents::*, data::*, debug_info::{DebugInfo, DEBUGINFO_NONE}, gendata::*, genrefs::*, refs::*, ViperIdent, VirCtxt
};

macro_rules! const_expr {
    ($expr_kind:expr) => {
        &ExprGenData {
            kind: $expr_kind,
            debug_info: DEBUGINFO_NONE,
            span: None,
        }
    };
}
cfg_if! {
    if #[cfg(debug_assertions)] {

        // The functions below conservatively check that local variables bound
        // in forall expressions, let-bindings, function arguments etc. have the
        // correct type with respect to their usages. It's better to identify
        // the relevant errors here so more debug information is available. The
        // check is incomplete, namely:
        // - Lazy expressions are not typechecked
        // - The binding for a local is not always known, usages of unbound
        //   variables are not checked
        // - Unsupported types are not checked

        use std::collections::HashMap;
        fn check_predicate_app_bindings<'vir, Curr, Next>(
            m: &mut HashMap<&'vir str, Type<'vir>>,
            e: PredicateAppGen<'vir, Curr, Next>
        ) {
            for arg in e.args.iter() {
                check_expr_bindings(m, *arg);
            }
            if let Some(perm) = e.perm {
                check_expr_bindings(m, perm);
            }
        }
        fn check_stmt_bindings<'vir, Curr, Next>(
            m: &mut HashMap<&'vir str, Type<'vir>>,
            e: StmtGen<'vir, Curr, Next>
        ) {
            match e.kind {
                StmtKindGenData::LocalDecl(local, e) => {
                    if let Some(e) = e {
                        check_expr_bindings(m, e);
                    }
                    m.insert(local.name, local.ty);
                }
                StmtKindGenData::PureAssign(p) => {
                    check_expr_bindings(m, p.lhs);
                    check_expr_bindings(m, p.rhs);
                }
                StmtKindGenData::Inhale(e) |
                StmtKindGenData::Exhale(e) => {
                    check_expr_bindings(m, e);
                }
                StmtKindGenData::Unfold(app) | StmtKindGenData::Fold(app) => {
                    check_predicate_app_bindings(m, app);
                }
                StmtKindGenData::MethodCall(MethodCallGenData {
                    args,
                    ..
                }) => {
                    for arg in args.iter() {
                        check_expr_bindings(m, *arg);
                    }
                }
                StmtKindGenData::Comment(_) => {},
                StmtKindGenData::Dummy(_) => todo!(),
            }
        }
        fn check_expr_bindings<'vir, Curr, Next>(
            m: &mut HashMap<&'vir str, Type<'vir>>,
            e: ExprGen<'vir, Curr, Next>
        ) {
            match e.kind {
                ExprKindGenData::Local(LocalData { name, ty, debug_info }) => {
                    if let Some(bound_ty) = m.get(name) {
                        if !matches!(bound_ty, TypeData::Unsupported(_)) &&
                           !matches!(ty, TypeData::Unsupported(_))
                         {
                            assert_eq!(
                                bound_ty,
                                ty,
                                "Type mismatch for local variable {name}. \
                                Scope assigns {name} to type {bound_ty:?}, but the actual type is {ty:?}.\
                                Debug info: {debug_info}"
                            )
                        }
                    }
                },
                ExprKindGenData::Let(LetGenData { name, val, expr }) => {
                    check_expr_bindings(m, *val);
                    if !matches!(val.kind, ExprKindGenData::Lazy(..)) {
                        m.insert(name, val.ty());
                    }
                    check_expr_bindings(m, *expr);
                    m.remove(name);
                },
                ExprKindGenData::FuncApp(FuncAppGenData { args, .. }) => {
                    for arg in args.iter() {
                        check_expr_bindings(m, *arg);
                    }
                },
                ExprKindGenData::Const(..) | ExprKindGenData::Lazy(..) => {},
                ExprKindGenData::PredicateApp(app) => {
                    check_predicate_app_bindings(m, app);
                },
                ExprKindGenData::AccField( AccFieldGenData { recv, perm, .. }) => {
                    check_expr_bindings(m, *recv);
                    if let Some(perm) = perm {
                        check_expr_bindings(m, *perm);
                    }
                },
                ExprKindGenData::Field(e, _) => {
                    check_expr_bindings(m, *e);
                },
                ExprKindGenData::Unfolding(UnfoldingGenData { target, expr }) => {
                    check_predicate_app_bindings(m, target);
                    check_expr_bindings(m, *expr);
                },
                ExprKindGenData::BinOp(BinOpGenData { lhs, rhs, .. }) => {
                    check_expr_bindings(m, *lhs);
                    check_expr_bindings(m, *rhs);
                },
                ExprKindGenData::UnOp(UnOpGenData { expr, .. }) => {
                    check_expr_bindings(m, *expr);
                },
                ExprKindGenData::Ternary(TernaryGenData { cond, then, else_}) => {
                    check_expr_bindings(m, *cond);
                    check_expr_bindings(m, *then);
                    check_expr_bindings(m, *else_);
                }
                ExprKindGenData::Forall(ForallGenData { qvars, triggers, body }) => {
                    for qvar in qvars.iter() {
                        m.insert(qvar.name, qvar.ty);
                    }
                    for trigger in triggers.iter() {
                        for expr in trigger.exprs.iter() {
                            check_expr_bindings(m, *expr);
                        }
                    }
                    check_expr_bindings(m, *body);
                    for qvar in qvars.iter() {
                        m.remove(qvar.name);
                    }
                }
                other => todo!("{other:?}")
            }
        }
    }
}


impl<'tcx> VirCtxt<'tcx> {
    pub fn mk_local<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> Local<'vir> {
        self.alloc(LocalData { name, ty, debug_info: DebugInfo::new(&self) })
    }

    pub fn mk_local_decl<'vir>(&'vir self, name: &'vir str, ty: Type<'vir>) -> LocalDecl<'vir> {
        self.alloc(LocalDeclData { name, ty })
    }

    pub fn mk_local_decl_local<'vir>(&'vir self, local: Local<'vir>) -> LocalDecl<'vir> {
        self.alloc(LocalDeclData { name: local.name, ty: local.ty })
    }

    pub fn mk_local_ex_local<'vir, Curr, Next>(
        &'vir self,
        local: Local<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Local(local)),
        ))
    }

    pub fn mk_local_ex<'vir, Curr, Next>(&'vir self, name: &'vir str, ty: Type<'vir>) -> ExprGen<'vir, Curr, Next> {
        self.mk_local_ex_local(self.mk_local(name, ty))
    }

    pub(crate) fn mk_func_app<'vir, Curr, Next>(
        &'vir self,
        target: &'vir str,
        src_args: &[ExprGen<'vir, Curr, Next>],
        result_ty: Type<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::FuncApp(self.arena.alloc(FuncAppGenData {
                target,
                args: self.alloc_slice(src_args),
                result_ty,
            }))),
        ))
    }

    pub fn mk_lazy_expr<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        func: Box<dyn for<'a> Fn(&'vir VirCtxt<'a>, Curr) -> Next + 'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Lazy(self.alloc(LazyGenData {
                name,
                func,
            }))),
        ))
    }

    pub fn mk_ternary_expr<'vir, Curr, Next>(
        &'vir self,
        cond: ExprGen<'vir, Curr, Next>,
        then: ExprGen<'vir, Curr, Next>,
        else_: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Ternary(self.alloc(TernaryGenData {
                cond,
                then,
                else_,
            }))),
        ))
    }

    pub fn mk_unary_op_expr<'vir, Curr, Next>(
        &'vir self,
        kind: UnOpKind,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::UnOp(
                self.alloc(UnOpGenData { kind, expr }),
            )),
        ))
    }

    pub fn mk_old_expr<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Old(expr)),
        ))
    }

    pub fn mk_forall_expr<'vir, Curr, Next>(
        &'vir self,
        qvars: &'vir [LocalDecl<'vir>],
        triggers: &'vir [TriggerGen<'vir, Curr, Next>],
        body: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Forall(self.alloc(ForallGenData {
                qvars,
                triggers,
                body,
            }))),
        ))
    }

    pub fn mk_trigger<'vir, Curr, Next>(
        &'vir self,
        exprs: &[ExprGen<'vir, Curr, Next>],
    ) -> TriggerGen<'vir, Curr, Next> {
        self.alloc(TriggerGenData {
            exprs: self.alloc_slice(exprs),
        })
    }

    pub fn mk_let_expr<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        val: ExprGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        let let_expr = self.alloc(
            ExprGenData::new(
                self.alloc(ExprKindGenData::Let(
                    self.alloc(LetGenData { name, val, expr })
                ))
            )
        );
        cfg_if! {
            if #[cfg(debug_assertions)] {
                check_expr_bindings(&mut HashMap::new(), let_expr);
            }
        }
        let_expr
    }

    pub fn mk_predicate_app_expr<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::PredicateApp(pred_app)),
        ))
    }

    pub fn mk_bin_op_expr<'vir, Curr, Next>(
        &'vir self,
        kind: BinOpKind,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::BinOp(self.alloc(BinOpGenData {
                kind,
                lhs,
                rhs,
            }))),
        ))
    }
    pub fn mk_eq_expr<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.mk_bin_op_expr(BinOpKind::CmpEq, lhs, rhs)
    }

    pub fn mk_field_expr<'vir, Curr, Next>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Field(recv, field)),
        ))
    }

    pub fn mk_unfolding_expr<'vir, Curr, Next>(
        &'vir self,
        target: PredicateAppGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Unfolding(
                self.alloc(UnfoldingGenData { target, expr }),
            )),
        ))
    }

    pub fn mk_acc_field_expr<'vir, Curr, Next>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next>,
        field: Field<'vir>,
        perm: Option<ExprGen<'vir, Curr, Next>>,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::AccField(self.alloc(AccFieldGenData { recv, field, perm }))),
        ))
    }

    pub fn mk_const_expr<'vir, Curr, Next>(
        &'vir self,
        value: ConstData,
    ) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Const(self.alloc(value))),
        ))
    }

    pub fn mk_todo_expr<'vir, Curr, Next>(&'vir self, msg: &'vir str) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Todo(msg)),
        ))
    }

    pub const fn mk_bool<'vir, const VALUE: bool>(&'vir self) -> Expr<'vir> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Bool(VALUE)))
    }

    pub const fn mk_int<'vir, const VALUE: i128>(&'vir self) -> Expr<'vir> {
        if VALUE < 0 {
            const_expr!(&ExprKindGenData::UnOp(&UnOpData {
                kind: UnOpKind::Neg,
                expr: const_expr!(&ExprKindGenData::Const(&ConstData::Int((-VALUE) as u128))),
            }))
        } else {
            const_expr!(&ExprKindGenData::Const(&ConstData::Int(VALUE as u128)))
        }
    }

    pub const fn mk_uint<'vir, const VALUE: u128>(&'vir self) -> Expr<'vir> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Int(VALUE)))
    }

    pub const fn mk_wildcard<'vir, Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Wildcard))
    }

    pub const fn mk_null<'vir, Curr, Next>(&'vir self) -> ExprGen<'vir, Curr, Next> {
        const_expr!(&ExprKindGenData::Const(&ConstData::Null))
    }

    pub fn mk_result<'vir, Curr, Next>(&'vir self, ty: Type<'vir>) -> ExprGen<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Result(ty))))
    }

    pub fn mk_field<'vir>(
        &'vir self,
        name: &'vir str,
        ty: Type<'vir>,
    ) -> Field<'vir> {
        self.alloc(FieldData { name, ty })
    }

    pub fn mk_domain_axiom<'vir, Curr, Next>(
        &'vir self,
        name: ViperIdent<'vir>,
        expr: ExprGen<'vir, Curr, Next>
    ) -> DomainAxiomGen<'vir, Curr, Next> {
        self.alloc(DomainAxiomGenData {
            name: name.to_str(),
            expr
        })
    }

    pub fn mk_domain_function<'vir, A: Arity<'vir, Arg = Type<'vir>>>(
        &'vir self,
        ident: FunctionIdent<'vir, A>,
        unique: bool,
    ) -> DomainFunction<'vir> {
        self.alloc(DomainFunctionData {
            unique,
            name: ident.name(),
            args: ident.arity().args(),
            ret: ident.result_ty(),
        })
    }

    pub fn mk_function<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str, // TODO: identifiers
        args: &'vir [LocalDecl<'vir>],
        ret: Type<'vir>,
        pres: &'vir [ExprGen<'vir, Curr, Next>],
        posts: &'vir [ExprGen<'vir, Curr, Next>],
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) -> FunctionGen<'vir, Curr, Next> {
        // TODO: Typecheck pre and post conditions
        if let Some(body) = expr {
            assert!(body.ty() == ret);
            cfg_if! {
                if #[cfg(debug_assertions)] {
                    let mut m = HashMap::new();
                    for arg in args {
                        m.insert(arg.name, arg.ty);
                    }
                    check_expr_bindings(&mut m, body);
                }
            }
        }
        self.alloc(FunctionGenData {
            name,
            args,
            ret,
            pres,
            posts,
            expr
        })
    }

    pub fn mk_predicate<'vir, Curr, Next, A: Arity<'vir> + CheckTypes<'vir> + Debug>(
        &'vir self,
        ident: PredicateIdent<'vir, A>,
        args: &'vir [LocalDecl<'vir>],
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) -> PredicateGen<'vir, Curr, Next> {
        if !ident.arity().types_match(args) {
            panic!(
                "Predicate {} could not be applied. Expected: {:?}, Actual: {:?} debug info: {}",
                ident.name(),
                ident.arity(),
                args,
                ident.debug_info()
            );
        }
        assert!(ident.arity().types_match(args));
        self.mk_predicate_unchecked(
            ident.name().to_str(),
            args,
            expr
        )
    }

    pub fn mk_predicate_unchecked<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDecl<'vir>],
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) -> PredicateGen<'vir, Curr, Next> {
        self.alloc(PredicateGenData {
            name,
            args,
            expr
        })
    }

    pub fn mk_domain<'vir, Curr, Next>(
        &'vir self,
        name: ViperIdent<'vir>,
        typarams: &'vir [DomainParam<'vir>],
        axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
        functions: &'vir [DomainFunction<'vir>]
    ) -> DomainGen<'vir, Curr, Next> {
        self.alloc(DomainGenData {
            name: name.to_str(),
            typarams,
            axioms,
            functions
        })
    }

    pub fn mk_exhale_stmt<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::Exhale(expr)),
        ))
    }

    pub fn mk_unfold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::Unfold(pred_app)),
        ))
    }

    pub fn mk_fold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::Fold(pred_app)),
        ))
    }

    pub fn mk_pure_assign_stmt<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next>,
        rhs: ExprGen<'vir, Curr, Next>
    ) -> StmtGen<'vir, Curr, Next> {
        assert_eq!(lhs.ty(),rhs.ty());
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::PureAssign(
                self.alloc(PureAssignGenData {
                    lhs,
                    rhs,
                }),
            )),
        ))
    }

    pub fn mk_local_decl_stmt<'vir, Curr, Next>(
        &'vir self,
        local: LocalDecl<'vir>,
        expr: Option<ExprGen<'vir, Curr, Next>>
    ) ->  StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::LocalDecl(local, expr)),
        ))
    }

    pub fn mk_assume_false_stmt<'vir, Curr, Next>(
        &'vir self
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::AssumeFalse
        )
    }

    pub fn mk_goto_stmt<'vir, Curr, Next>(
        &'vir self,
        block: CfgBlockLabel<'vir>
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::Goto(block)
        )
    }

    pub fn mk_dummy_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::Dummy(msg)
        )
    }

    pub fn mk_comment_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str
    ) -> StmtGen<'vir, Curr, Next> {
        self.alloc(StmtGenData::new(
            self.alloc(StmtKindGenData::Comment(msg)),
        ))
    }

    pub fn mk_goto_if_stmt<'vir, Curr, Next>(
        &'vir self,
        value: ExprGen<'vir, Curr, Next>,
        targets: &'vir [GotoIfTargetGen<'vir, Curr, Next>],
        otherwise: CfgBlockLabel<'vir>,
        otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(
            TerminatorStmtGenData::GotoIf(self.alloc(GotoIfGenData {
                value,
                targets,
                otherwise,
                otherwise_statements,
            }))
        )
    }

    pub fn mk_goto_if_target<'vir, Curr, Next>(
        &'vir self,
        value: ExprGen<'vir, Curr, Next>,
        label: CfgBlockLabel<'vir>,
        statements: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> GotoIfTargetGen<'vir, Curr, Next> {
        self.alloc(
            GotoIfTargetGenData {
                value,
                label,
                statements,
            }
        )
    }

    pub fn mk_cfg_block<'vir, Curr, Next>(
        &'vir self,
        label: CfgBlockLabel<'vir>,
        stmts: &'vir [StmtGen<'vir, Curr, Next>],
        terminator: TerminatorStmtGen<'vir, Curr, Next>,
    ) -> CfgBlockGen<'vir, Curr, Next> {
        self.alloc(CfgBlockGenData {
            label,
            stmts,
            terminator
        })
    }

    pub fn mk_method<'vir, Curr, Next, A: Arity<'vir> + CheckTypes<'vir> + Debug>(
        &'vir self,
        ident: MethodIdent<'vir, A>,
        args: &'vir [LocalDecl<'vir>],
        rets: &'vir [LocalDecl<'vir>],
        pres: &'vir [ExprGen<'vir, Curr, Next>],
        posts: &'vir [ExprGen<'vir, Curr, Next>],
        blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
    ) -> MethodGen<'vir, Curr, Next> {
        assert!(ident.arity().types_match(args),
            "Method {} could not be created. Identifier arity: {:?}, Method decls: {args:?}",
            ident.name_str(),
            ident.arity()
        );
        self.mk_method_unchecked(
            ident.name().to_str(),
            args,
            rets,
            pres,
            posts,
            blocks
        )
    }

    pub fn mk_method_unchecked<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDecl<'vir>],
        rets: &'vir [LocalDecl<'vir>],
        pres: &'vir [ExprGen<'vir, Curr, Next>],
        posts: &'vir [ExprGen<'vir, Curr, Next>],
        blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
    ) -> MethodGen<'vir, Curr, Next> {
        cfg_if! {
            if #[cfg(debug_assertions)] {
                if let Some(blocks) = blocks {
                    let mut m = HashMap::new();
                    for arg in args {
                        m.insert(arg.name, arg.ty);
                    }
                    for block in blocks {
                        for stmt in block.stmts {
                            check_stmt_bindings(&mut m, stmt);
                        }
                    }
                }
            }
        }
        self.alloc(MethodGenData {
            name,
            args,
            rets,
            pres,
            posts,
            body: blocks.map(|blocks| self.alloc(MethodBodyGenData {
                blocks,
            })),
        })
    }


    pub fn mk_program<'vir, Curr, Next>(
        &'vir self,
        fields: &'vir [Field<'vir>],
        domains: &'vir [DomainGen<'vir, Curr, Next>],
        predicates: &'vir [PredicateGen<'vir, Curr, Next>],
        functions: &'vir [FunctionGen<'vir, Curr, Next>],
        methods: &'vir [MethodGen<'vir, Curr, Next>]
    ) -> ProgramGen<'vir, Curr, Next> {
        self.alloc(ProgramGenData {
            fields,
            domains,
            predicates,
            functions,
            methods
        })
    }

    pub fn mk_conj<'vir>(&'vir self, elems: &[Expr<'vir>]) -> Expr<'vir> {
        elems.split_last().map(|(last, rest)| {
            rest.iter().rfold(*last, |acc, e| {
                self.mk_bin_op_expr(BinOpKind::And, *e, acc)
            })
        }).unwrap_or_else(|| self.mk_bool::<true>())
    }

    pub fn mk_disj<'vir>(&'vir self, elems: &[Expr<'vir>]) -> Expr<'vir> {
        elems.split_last().map(|(last, rest)| {
            rest.iter().rfold(*last, |acc, e| {
                self.mk_bin_op_expr(BinOpKind::Or, *e, acc)
            })
        }).unwrap_or_else(|| self.mk_bool::<false>())
    }

    const fn get_int_data(rust_ty: &ty::TyKind) -> (u32, bool) {
        match rust_ty {
            ty::Int(ty::IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u32, true),
            ty::Int(ty::IntTy::I8) => (8, true),
            ty::Int(ty::IntTy::I16) => (16, true),
            ty::Int(ty::IntTy::I32) => (32, true),
            ty::Int(ty::IntTy::I64) => (64, true),
            ty::Int(ty::IntTy::I128) => (128, true),
            ty::Uint(ty::UintTy::Usize) => ((std::mem::size_of::<usize>() * 8) as u32, true),
            ty::Uint(ty::UintTy::U8) => (8, false),
            ty::Uint(ty::UintTy::U16) => (16, false),
            ty::Uint(ty::UintTy::U32) => (32, false),
            ty::Uint(ty::UintTy::U64) => (64, false),
            ty::Uint(ty::UintTy::U128) => (128, false),
            _ => unreachable!(),
        }
    }
    pub const fn get_min_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(rust_ty) {
            (_, false) => self.mk_uint::<0>(),
            (i8::BITS, true) => self.mk_int::<{ i8::MIN as i128 }>(),
            (i16::BITS, true) => self.mk_int::<{ i16::MIN as i128 }>(),
            (i32::BITS, true) => self.mk_int::<{ i32::MIN as i128 }>(),
            (i64::BITS, true) => self.mk_int::<{ i64::MIN as i128 }>(),
            (i128::BITS, true) => self.mk_int::<{ i128::MIN }>(),
            (_, true) => unreachable!(),
        }
    }
    pub const fn get_max_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(rust_ty) {
            (u8::BITS, false) => self.mk_uint::<{ u8::MAX as u128 }>(),
            (u16::BITS, false) => self.mk_uint::<{ u16::MAX as u128 }>(),
            (u32::BITS, false) => self.mk_uint::<{ u32::MAX as u128 }>(),
            (u64::BITS, false) => self.mk_uint::<{ u64::MAX as u128 }>(),
            (u128::BITS, false) => self.mk_uint::<{ u128::MAX }>(),
            (i8::BITS, true) => self.mk_int::<{ i8::MAX as i128 }>(),
            (i16::BITS, true) => self.mk_int::<{ i16::MAX as i128 }>(),
            (i32::BITS, true) => self.mk_int::<{ i32::MAX as i128 }>(),
            (i64::BITS, true) => self.mk_int::<{ i64::MAX as i128 }>(),
            (i128::BITS, true) => self.mk_int::<{ i128::MAX }>(),
            _ => unreachable!(),
        }
    }
    pub fn get_modulo_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ 1_u128 << u8::BITS }>(),
            (u16::BITS, _) => self.mk_uint::<{ 1_u128 << u16::BITS }>(),
            (u32::BITS, _) => self.mk_uint::<{ 1_u128 << u32::BITS }>(),
            (u64::BITS, _) => self.mk_uint::<{ 1_u128 << u64::BITS }>(),
            (u128::BITS, _) => {
                // TODO: make this a `const` once `Expr` isn't invariant in `'vir` so that it can be `'const` instead
                let half = self.mk_uint::<{ 1_u128 << u64::BITS }>();
                self.mk_bin_op_expr(BinOpKind::Add, half, half)
            }
            _ => unreachable!(),
        }
    }
    pub fn get_signed_shift_int<'vir>(
        &'vir self,
        ty: Type,
        rust_ty: &ty::TyKind,
    ) -> Option<Expr<'vir>> {
        let int = match Self::get_int_data(rust_ty) {
            (_, false) => return None,
            (u8::BITS, true) => self.mk_uint::<{ 1_u128 << (u8::BITS - 1) }>(),
            (u16::BITS, true) => self.mk_uint::<{ 1_u128 << (u16::BITS - 1) }>(),
            (u32::BITS, true) => self.mk_uint::<{ 1_u128 << (u32::BITS - 1) }>(),
            (u64::BITS, true) => self.mk_uint::<{ 1_u128 << (u64::BITS - 1) }>(),
            (u128::BITS, true) => self.mk_uint::<{ 1_u128 << (u128::BITS - 1) }>(),
            (_, true) => unreachable!(),
        };
        Some(int)
    }
    pub fn get_bit_width_int<'vir>(&'vir self, ty: Type, rust_ty: &ty::TyKind) -> Expr<'vir> {
        match Self::get_int_data(rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ u8::BITS as u128 }>(),
            (u16::BITS, _) => self.mk_uint::<{ u16::BITS as u128 }>(),
            (u32::BITS, _) => self.mk_uint::<{ u32::BITS as u128 }>(),
            (u64::BITS, _) => self.mk_uint::<{ u64::BITS as u128 }>(),
            (u128::BITS, _) => self.mk_uint::<{ u128::BITS as u128 }>(),
            _ => unreachable!(),
        }
    }
}
