use crate::{
    callable::*, data::*, debug_info::DebugInfo, gendata::*, genrefs::*, refs::*, typecheck_error,
    CastType, CompType, HasType, ViperIdent, VirCtxt,
};
use cfg_if::cfg_if;
use prusti_rustc_interface::middle::ty;
use std::fmt::Debug;

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
            m: &mut HashMap<&'vir str, TypeDyn<'vir>>,
            e: PredicateAppGen<'vir, Curr, Next>
        ) {
            for arg in e.args.iter() {
                check_expr_bindings(m, *arg);
            }
            if let Some(perm) = e.perm {
                check_expr_bindings(m, perm.as_dyn());
            }
        }
        fn check_stmt_bindings<'vir, Curr, Next>(
            m: &mut HashMap<&'vir str, TypeDyn<'vir>>,
            e: StmtGen<'vir, Curr, Next>
        ) {
            match e.kind {
                StmtKindGenData::LocalDecl(local, e) => {
                    if let Some(e) = e {
                        check_expr_bindings(m, *e);
                    }
                    m.insert(local.name, local.ty_dyn());
                }
                StmtKindGenData::PureAssign(p) => {
                    check_expr_bindings(m, p.lhs);
                    check_expr_bindings(m, p.rhs);
                }
                StmtKindGenData::Inhale(e) |
                StmtKindGenData::Exhale(e) |
                StmtKindGenData::Refute(e) => {
                    check_expr_bindings(m, e.as_dyn());
                }
                StmtKindGenData::Unfold(app) | StmtKindGenData::Fold(app) => {
                    check_predicate_app_bindings(m, app);
                }
                StmtKindGenData::Package(_wand, stmts) => {
                    // TODO: check types in wand
                    for stmt in stmts.iter() {
                        check_stmt_bindings(m, stmt);
                    }
                }
                StmtKindGenData::Apply(_wand) => {
                    // TODO: check types in wand
                }
                StmtKindGenData::MethodCall(MethodCallGenData {
                    args,
                    ..
                }) => {
                    for arg in args.iter() {
                        check_expr_bindings(m, *arg);
                    }
                }
                StmtKindGenData::If(e, thn, els) => {
                    check_expr_bindings(m, e.as_dyn());
                    for thn in thn.iter() {
                        check_stmt_bindings(m, thn);
                    }
                    for els in els.iter() {
                        check_stmt_bindings(m, els);
                    }
                }
                StmtKindGenData::Label(_) => {},
                StmtKindGenData::Comment(_) => {},
                StmtKindGenData::Dummy(_) => todo!(),
            }
        }
        fn check_expr_bindings<'vir, Curr, Next>(
            m: &mut HashMap<&'vir str, TypeDyn<'vir>>,
            e: ExprGenDyn<'vir, Curr, Next>
        ) {
            match e.kind {
                ExprKindGenData::Local(LocalData { name, ty, debug_info }) => {
                    if let Some(bound_ty) = m.get(name) {
                        if !matches!(bound_ty.kind(), TypeKind::Unsupported(_)) &&
                           !matches!(ty.kind(), TypeKind::Unsupported(_)) &&
                           bound_ty != ty
                         {
                            typecheck_error!(
                                "Type mismatch for local variable {name}. \
                                Scope assigns {name} to type {bound_ty:?}, but the actual type is {ty:?}.\
                                Debug info: {debug_info}"
                            );
                            panic!();
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
                ExprKindGenData::FuncApp(FuncAppGenData { args, .. })
                | ExprKindGenData::CollectionLiteral(CollectionLiteralGenData {
                    values: args,
                    ..
                }) => {
                    for arg in args.iter() {
                        check_expr_bindings(m, *arg);
                    }
                },
                ExprKindGenData::CollectionUpdate(CollectionUpdateGenData { target, key, val }) => {
                    check_expr_bindings(m, *target);
                    check_expr_bindings(m, *key);
                    check_expr_bindings(m, *val);
                },
                ExprKindGenData::CollectionLen(collection)
                | ExprKindGenData::MapDomain(collection)
                | ExprKindGenData::MapRange(collection) => {
                    check_expr_bindings(m, *collection);
                },
                ExprKindGenData::Old(OldGenData { expr, .. }) => {
                    check_expr_bindings(m, *expr);
                },
                ExprKindGenData::Const(..) | ExprKindGenData::Lazy(..) => {},
                ExprKindGenData::PredicateApp(app) => {
                    check_predicate_app_bindings(m, app);
                },
                ExprKindGenData::AccField( AccFieldGenData { recv, perm, .. }) => {
                    check_expr_bindings(m, recv.as_dyn());
                    if let Some(perm) = perm {
                        check_expr_bindings(m, perm.as_dyn());
                    }
                },
                ExprKindGenData::Field(e, _) => {
                    check_expr_bindings(m, e.as_dyn());
                },
                ExprKindGenData::AdtDestructor(e, _) | ExprKindGenData::AdtDiscriminator(e, _) => {
                    check_expr_bindings(m, e.as_dyn());
                },
                ExprKindGenData::Unfolding(UnfoldingGenData { target, expr }) => {
                    check_predicate_app_bindings(m, target);
                    check_expr_bindings(m, *expr);
                },
                ExprKindGenData::BinOp(BinOpGenData { lhs, rhs, .. })
                | ExprKindGenData::CollectionBinOp(CollectionBinOpGenData { lhs, rhs, .. }) => {
                    check_expr_bindings(m, *lhs);
                    check_expr_bindings(m, *rhs);
                },
                ExprKindGenData::UnOp(UnOpGenData { expr, .. }) => {
                    check_expr_bindings(m, expr.as_dyn());
                },
                ExprKindGenData::Ternary(TernaryGenData { cond, then, else_}) => {
                    check_expr_bindings(m, cond.as_dyn());
                    check_expr_bindings(m, *then);
                    check_expr_bindings(m, *else_);
                }
                ExprKindGenData::Forall(ForallGenData { qvars, triggers, body })
                | ExprKindGenData::Exists(ExistsGenData { qvars, triggers, body }) => {
                    for qvar in qvars.iter() {
                        m.insert(qvar.name, qvar.ty_dyn());
                    }
                    for trigger in triggers.iter() {
                        for expr in trigger.exprs.iter() {
                            check_expr_bindings(m, *expr);
                        }
                    }
                    check_expr_bindings(m, body.as_dyn());
                    for qvar in qvars.iter() {
                        m.remove(qvar.name);
                    }
                }
                ExprKindGenData::InhaleExhale(InhaleExhaleGenData { inhale, exhale }) => {
                    check_expr_bindings(m, inhale.as_dyn());
                    check_expr_bindings(m, exhale.as_dyn());
                }
                ExprKindGenData::Wand(WandGenData { lhs, rhs }) => {
                    check_expr_bindings(m, lhs.as_dyn());
                    check_expr_bindings(m, rhs.as_dyn());
                },
                other@(ExprKindGenData::Result(_) | ExprKindGenData::Todo(_)) =>  todo!("{other:?}"),
            }
        }
    }
}

impl<'tcx> VirCtxt<'tcx> {
    pub fn mk_local_decl<'vir, T: CompType>(
        &'vir self,
        name: &'vir str,
        ty: Type<'vir, T>,
    ) -> LocalDecl<'vir, T> {
        self.alloc(LocalDeclData { name, ty })
    }

    fn mk_local<'vir, T: CompType>(&'vir self, decl: LocalDecl<'vir, T>) -> Local<'vir, T> {
        self.alloc(LocalData {
            name: decl.name,
            ty: decl.ty,
            debug_info: DebugInfo::new(self),
        })
    }

    pub fn mk_local_ex<'vir, Curr, Next, T: CompType>(
        &'vir self,
        decl: LocalDecl<'vir, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Local(self.mk_local(decl.as_dyn()))),
        ))
    }

    pub(crate) fn mk_func_app<'vir, Curr, Next, R: CompType>(
        &'vir self,
        target: &'vir str,
        args: &'vir [ExprGenDyn<'vir, Curr, Next>],
        result_ty: Type<'vir, R>,
        typ_var_map: &'vir [TypeDyn<'vir>],
    ) -> ExprGen<'vir, Curr, Next, R> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::FuncApp(
            self.arena.alloc(FuncAppGenData {
                target,
                args,
                result_ty: result_ty.as_dyn(),
                typ_var_map,
            }),
        ))))
    }

    #[allow(clippy::type_complexity)]
    pub fn mk_lazy_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        name: &'vir str,
        ty: Type<'vir, T>,
        func: Box<dyn for<'a> Fn(&'vir VirCtxt<'a>, Curr) -> Next + 'vir>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Lazy(
            self.alloc(LazyGenData {
                name,
                func,
                ty: ty.as_dyn(),
            }),
        ))))
    }

    pub fn mk_ty_set<'vir, T: CompType>(&'vir self, elem_ty: Type<'vir, T>) -> TypeSet<'vir> {
        self.alloc(TypeData::new(TypeKind::Set(elem_ty.as_dyn())))
    }

    pub fn mk_ty_multiset<'vir, T: CompType>(
        &'vir self,
        elem_ty: Type<'vir, T>,
    ) -> TypeMultiset<'vir> {
        self.alloc(TypeData::new(TypeKind::Multiset(elem_ty.as_dyn())))
    }

    pub fn mk_ty_seq<'vir, T: CompType>(&'vir self, elem_ty: Type<'vir, T>) -> TypeSeq<'vir> {
        self.alloc(TypeData::new(TypeKind::Seq(elem_ty.as_dyn())))
    }

    pub fn mk_ty_map<'vir, K: CompType, V: CompType>(
        &'vir self,
        key_ty: Type<'vir, K>,
        val_ty: Type<'vir, V>,
    ) -> TypeMap<'vir> {
        self.alloc(TypeData::new(TypeKind::Map(
            key_ty.as_dyn(),
            val_ty.as_dyn(),
        )))
    }

    fn mk_collection_literal_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        values: &'vir [&'vir ExprGenData<'vir, Curr, Next, T>],
        elem_ty: Type<'vir, T>,
        ty: TypeDyn<'vir>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        for value in values {
            if value.ty() != elem_ty {
                typecheck_error!(
                    "Type mismatch in {:?} literal. Expected element type: {:?}, actual: {:?}",
                    ty,
                    elem_ty,
                    value.ty(),
                );
            }
        }
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::CollectionLiteral(self.alloc(CollectionLiteralGenData {
                values: values.as_dyn(),
                ty,
            })),
        )))
    }

    pub fn mk_set_literal_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        values: &'vir [&'vir ExprGenData<'vir, Curr, Next, T>],
        elem_ty: Type<'vir, T>,
    ) -> ExprGenSet<'vir, Curr, Next> {
        self.mk_collection_literal_expr(values, elem_ty, self.mk_ty_set(elem_ty).as_dyn())
            .downcast_ty()
    }

    pub fn mk_multiset_literal_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        values: &'vir [&'vir ExprGenData<'vir, Curr, Next, T>],
        elem_ty: Type<'vir, T>,
    ) -> ExprGenMultiset<'vir, Curr, Next> {
        self.mk_collection_literal_expr(values, elem_ty, self.mk_ty_multiset(elem_ty).as_dyn())
            .downcast_ty()
    }

    pub fn mk_seq_literal_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        values: &'vir [&'vir ExprGenData<'vir, Curr, Next, T>],
        elem_ty: Type<'vir, T>,
    ) -> ExprGenSeq<'vir, Curr, Next> {
        self.mk_collection_literal_expr(values, elem_ty, self.mk_ty_seq(elem_ty).as_dyn())
            .downcast_ty()
    }

    /// The empty `Map` literal (non-empty maps are built with
    /// [`Self::mk_map_update_expr`]).
    pub fn mk_map_empty_expr<'vir, Curr, Next, K: CompType, V: CompType>(
        &'vir self,
        key_ty: Type<'vir, K>,
        val_ty: Type<'vir, V>,
    ) -> ExprGenMap<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::CollectionLiteral(self.alloc(CollectionLiteralGenData {
                values: &[],
                ty: self.mk_ty_map(key_ty, val_ty).as_dyn(),
            })),
        )))
    }

    pub fn mk_ternary_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        cond: ExprGenBool<'vir, Curr, Next>,
        then: ExprGen<'vir, Curr, Next, T>,
        else_: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Ternary(
            self.alloc(TernaryGenData {
                cond,
                then: then.as_dyn(),
                else_: else_.as_dyn(),
            }),
        ))))
    }

    pub fn mk_unary_op_expr<'vir, Curr, Next>(
        &'vir self,
        kind: UnOpKind,
        expr: ExprGenPrim<'vir, Curr, Next>,
    ) -> ExprGenPrim<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::UnOp(
            self.alloc(UnOpGenData { kind, expr }),
        ))))
    }

    pub fn mk_old<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
        label: OldLabel<'vir>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Old(
            self.alloc(OldGenData {
                expr: expr.as_dyn(),
                label,
            }),
        ))))
    }

    pub fn mk_old_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.mk_old(expr, OldLabel::None)
    }

    pub fn mk_old_lhs_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.mk_old(expr, OldLabel::Lhs)
    }

    pub fn mk_labelled_old_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
        label: Option<CfgBlockLabelData<'vir>>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.mk_old(expr, label.map(OldLabel::Block).unwrap_or(OldLabel::None))
    }

    pub fn maybe_apply_label<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
        label: Option<OldLabel<'vir>>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        if let Some(label) = label {
            match label {
                OldLabel::Block(block) => self.mk_labelled_old_expr(expr, Some(block)),
                OldLabel::Label(label) => self.mk_local_labelled_old_expr(expr, label),
                OldLabel::None => self.mk_old_expr(expr),
                OldLabel::Lhs => self.mk_old_lhs_expr(expr),
            }
        } else {
            expr
        }
    }

    pub fn mk_local_labelled_old_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
        label: &'vir str,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.mk_old(expr, OldLabel::Label(label))
    }

    pub fn mk_rel_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        expr: ExprGen<'vir, Curr, Next, T>,
        exec: u32,
    ) -> ExprGen<'vir, Curr, Next, T> {
        let v = self.mk_const_expr(ConstData::Int(exec as u128));
        let args = [expr.as_dyn(), v.as_dyn()];
        self.mk_func_app("rel", self.alloc_array(&args), expr.ty(), &[])
    }

    pub fn mk_forall_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        qvars: &'vir [LocalDecl<'vir, T>],
        triggers: &'vir [TriggerGen<'vir, Curr, Next>],
        body: ExprGenBool<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        if qvars.is_empty() {
            return body;
        }
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Forall(
            self.alloc(ForallGenData {
                qvars: qvars.as_dyn(),
                triggers,
                body,
            }),
        ))))
    }

    pub fn mk_exists_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        qvars: &'vir [LocalDecl<'vir, T>],
        triggers: &'vir [TriggerGen<'vir, Curr, Next>],
        body: ExprGenBool<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        if qvars.is_empty() {
            return body;
        }
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Exists(
            self.alloc(ExistsGenData {
                qvars: qvars.as_dyn(),
                triggers,
                body,
            }),
        ))))
    }

    pub fn mk_trigger<'vir, Curr, Next, T: CompType>(
        &'vir self,
        exprs: &[ExprGen<'vir, Curr, Next, T>],
    ) -> TriggerGen<'vir, Curr, Next> {
        self.alloc(TriggerGenData {
            exprs: self.alloc_slice(exprs.as_dyn()),
        })
    }

    pub fn mk_let_expr<'vir, Curr, Next, V: CompType, T: CompType>(
        &'vir self,
        decl: LocalDecl<'vir, V>,
        val: ExprGen<'vir, Curr, Next, V>,
        expr: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        if decl.ty != val.ty() {
            typecheck_error!(
                "Type mismatch in let-binding for {}. Expected: {:?}, Actual: {:?}",
                decl.name,
                decl.ty,
                val.ty()
            );
        }
        let let_expr: ExprGen<'vir, Curr, Next, T> = self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::Let(self.alloc(LetGenData {
                name: decl.name,
                val: val.as_dyn(),
                expr: expr.as_dyn(),
            })),
        )));
        cfg_if! {
            if #[cfg(debug_assertions)] {
                check_expr_bindings(&mut HashMap::new(), let_expr.as_dyn());
            }
        }
        let_expr
    }

    pub fn mk_predicate_app_expr<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::PredicateApp(pred_app)),
        ))
    }

    pub fn mk_wand<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGenBool<'vir, Curr, Next>,
        rhs: ExprGenBool<'vir, Curr, Next>,
    ) -> WandGen<'vir, Curr, Next> {
        self.alloc(WandGenData { lhs, rhs })
    }

    pub fn mk_wand_expr<'vir, Curr, Next>(
        &'vir self,
        wand: WandGen<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Wand(wand))))
    }

    /// Use `mk_set_in_expr` for set in
    pub fn mk_bin_op_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        kind: BinOpKind,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenPrim<'vir, Curr, Next> {
        assert!(kind != BinOpKind::CmpEq, "Use mk_eq_expr instead");
        self.mk_bin_op_expr_inner(kind, lhs.as_dyn(), rhs.as_dyn())
            .downcast_ty()
    }

    pub fn mk_eq_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.mk_bin_op_expr_inner(BinOpKind::CmpEq, lhs.as_dyn(), rhs.as_dyn())
            .downcast_ty()
    }

    pub fn mk_set_in_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        elem: ExprGen<'vir, Curr, Next, T>,
        set: ExprGenSet<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        if !matches!(set.ty().kind(), TypeKind::Set(set_elem_ty) if elem.ty().as_dyn() == *set_elem_ty)
        {
            typecheck_error!(
                "Type mismatch in 'set in' expression. Have set type: {:?}, actual element type: {:?}",
                set.ty(),
                elem.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Contains,
            elem.as_dyn(),
            set.as_dyn(),
        )
        .downcast_ty()
    }

    /// Membership test for a native `Set` (element in the set) or `Map` (key in
    /// the map's domain), yielding a `Bool`. Backs the `expr!` macro's
    /// `(x) in (c)` syntax; prefer the statically typed
    /// [`Self::mk_set_in_expr`]/[`Self::mk_map_contains_expr`] when the
    /// collection kind is known.
    pub fn mk_contains_expr<'vir, Curr, Next, E: CompType, C: CompType>(
        &'vir self,
        elem: ExprGen<'vir, Curr, Next, E>,
        collection: ExprGen<'vir, Curr, Next, C>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        let valid = match collection.ty().kind() {
            TypeKind::Set(elem_ty) | TypeKind::Map(elem_ty, _) => elem.ty().as_dyn() == *elem_ty,
            _ => false,
        };
        if !valid {
            typecheck_error!(
                "Invalid membership expression. Element type: {:?}, collection type: {:?}",
                elem.ty(),
                collection.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Contains,
            elem.as_dyn(),
            collection.as_dyn(),
        )
        .downcast_ty()
    }

    /// A same-type binary set/multiset operation (union/intersection/
    /// difference), or a `subset` comparison.
    pub fn mk_anyset_op_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        kind: CollectionBinOpKind,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        if lhs.ty() != rhs.ty() {
            typecheck_error!(
                "Type mismatch in {:?} expression. LHS type: {:?}, RHS type: {:?}",
                kind,
                lhs.ty(),
                rhs.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(kind, lhs.as_dyn(), rhs.as_dyn())
    }

    pub fn mk_set_difference_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        self.mk_anyset_op_expr(CollectionBinOpKind::Difference, lhs, rhs)
    }

    pub fn mk_set_subset_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.mk_anyset_op_expr(CollectionBinOpKind::Subset, lhs, rhs)
            .downcast_ty()
    }

    /// The multiplicity of `elem` in the multiset `ms` (an `Int`).
    pub fn mk_multiset_count_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        elem: ExprGen<'vir, Curr, Next, T>,
        ms: ExprGenMultiset<'vir, Curr, Next>,
    ) -> ExprGenInt<'vir, Curr, Next> {
        if !matches!(ms.ty().kind(), TypeKind::Multiset(elem_ty) if elem.ty().as_dyn() == *elem_ty)
        {
            typecheck_error!(
                "Type mismatch in multiset count expression. Have multiset type: {:?}, actual element type: {:?}",
                ms.ty(),
                elem.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Contains,
            elem.as_dyn(),
            ms.as_dyn(),
        )
        .downcast_ty()
    }

    pub fn mk_seq_concat_expr<'vir, Curr, Next>(
        &'vir self,
        lhs: ExprGenSeq<'vir, Curr, Next>,
        rhs: ExprGenSeq<'vir, Curr, Next>,
    ) -> ExprGenSeq<'vir, Curr, Next> {
        if lhs.ty() != rhs.ty() {
            typecheck_error!(
                "Type mismatch in seq concat expression. LHS type: {:?}, RHS type: {:?}",
                lhs.ty(),
                rhs.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Concat,
            lhs.as_dyn(),
            rhs.as_dyn(),
        )
        .downcast_ty()
    }

    pub fn mk_seq_index_expr<'vir, Curr, Next>(
        &'vir self,
        seq: ExprGenSeq<'vir, Curr, Next>,
        index: ExprGenInt<'vir, Curr, Next>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Index,
            seq.as_dyn(),
            index.as_dyn(),
        )
    }

    /// Indexing into a native `Seq` (by an `Int` index) or `Map` (by a key),
    /// yielding the dynamically typed element/value. Backs the `expr!` macro's
    /// `(base)[index]` syntax; prefer the statically typed
    /// [`Self::mk_seq_index_expr`]/[`Self::mk_map_lookup_expr`] when the
    /// collection kind is known.
    pub fn mk_index_expr<'vir, Curr, Next, B: CompType, I: CompType>(
        &'vir self,
        base: ExprGen<'vir, Curr, Next, B>,
        index: ExprGen<'vir, Curr, Next, I>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        let valid = match base.ty().kind() {
            TypeKind::Seq(_) => matches!(index.ty().kind(), TypeKind::Int),
            TypeKind::Map(key_ty, _) => index.ty().as_dyn() == *key_ty,
            _ => false,
        };
        if !valid {
            typecheck_error!(
                "Invalid indexing expression. Base type: {:?}, index type: {:?}",
                base.ty(),
                index.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Index,
            base.as_dyn(),
            index.as_dyn(),
        )
    }

    /// The first `num` elements of `seq` (clamping, like the native Viper
    /// operation).
    pub fn mk_seq_take_expr<'vir, Curr, Next>(
        &'vir self,
        seq: ExprGenSeq<'vir, Curr, Next>,
        num: ExprGenInt<'vir, Curr, Next>,
    ) -> ExprGenSeq<'vir, Curr, Next> {
        self.mk_collection_bin_op_expr_inner(CollectionBinOpKind::Take, seq.as_dyn(), num.as_dyn())
            .downcast_ty()
    }

    /// `seq` without its first `num` elements (clamping, like the native
    /// Viper operation).
    pub fn mk_seq_drop_expr<'vir, Curr, Next>(
        &'vir self,
        seq: ExprGenSeq<'vir, Curr, Next>,
        num: ExprGenInt<'vir, Curr, Next>,
    ) -> ExprGenSeq<'vir, Curr, Next> {
        self.mk_collection_bin_op_expr_inner(CollectionBinOpKind::Drop, seq.as_dyn(), num.as_dyn())
            .downcast_ty()
    }

    pub fn mk_seq_contains_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        elem: ExprGen<'vir, Curr, Next, T>,
        seq: ExprGenSeq<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        if !matches!(seq.ty().kind(), TypeKind::Seq(elem_ty) if elem.ty().as_dyn() == *elem_ty) {
            typecheck_error!(
                "Type mismatch in seq contains expression. Have seq type: {:?}, actual element type: {:?}",
                seq.ty(),
                elem.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Contains,
            elem.as_dyn(),
            seq.as_dyn(),
        )
        .downcast_ty()
    }

    pub fn mk_map_lookup_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        map: ExprGenMap<'vir, Curr, Next>,
        key: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        if !matches!(map.ty().kind(), TypeKind::Map(key_ty, _) if key.ty().as_dyn() == *key_ty) {
            typecheck_error!(
                "Type mismatch in map lookup expression. Have map type: {:?}, actual key type: {:?}",
                map.ty(),
                key.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(CollectionBinOpKind::Index, map.as_dyn(), key.as_dyn())
    }

    pub fn mk_map_contains_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        map: ExprGenMap<'vir, Curr, Next>,
        key: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        if !matches!(map.ty().kind(), TypeKind::Map(key_ty, _) if key.ty().as_dyn() == *key_ty) {
            typecheck_error!(
                "Type mismatch in map contains expression. Have map type: {:?}, actual key type: {:?}",
                map.ty(),
                key.ty(),
            );
        }
        self.mk_collection_bin_op_expr_inner(
            CollectionBinOpKind::Contains,
            key.as_dyn(),
            map.as_dyn(),
        )
        .downcast_ty()
    }

    pub fn mk_map_update_expr<'vir, Curr, Next, K: CompType, V: CompType>(
        &'vir self,
        map: ExprGenMap<'vir, Curr, Next>,
        key: ExprGen<'vir, Curr, Next, K>,
        val: ExprGen<'vir, Curr, Next, V>,
    ) -> ExprGenMap<'vir, Curr, Next> {
        if !matches!(
            map.ty().kind(),
            TypeKind::Map(key_ty, val_ty)
                if key.ty().as_dyn() == *key_ty && val.ty().as_dyn() == *val_ty
        ) {
            typecheck_error!(
                "Type mismatch in map update expression. Have map type: {:?}, actual key type: {:?}, value type: {:?}",
                map.ty(),
                key.ty(),
                val.ty(),
            );
        }
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::CollectionUpdate(self.alloc(CollectionUpdateGenData {
                target: map.as_dyn(),
                key: key.as_dyn(),
                val: val.as_dyn(),
            })),
        )))
    }

    /// The native Viper sequence update `seq[index := val]`.
    pub fn mk_seq_update_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        seq: ExprGenSeq<'vir, Curr, Next>,
        index: ExprGenInt<'vir, Curr, Next>,
        val: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenSeq<'vir, Curr, Next> {
        if !matches!(seq.ty().kind(), TypeKind::Seq(elem_ty) if val.ty().as_dyn() == *elem_ty) {
            typecheck_error!(
                "Type mismatch in seq update expression. Have seq type: {:?}, actual value type: {:?}",
                seq.ty(),
                val.ty(),
            );
        }
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::CollectionUpdate(self.alloc(CollectionUpdateGenData {
                target: seq.as_dyn(),
                key: index.as_dyn(),
                val: val.as_dyn(),
            })),
        )))
    }

    /// The length/cardinality of a native Viper collection.
    pub fn mk_collection_len_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        collection: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGenInt<'vir, Curr, Next> {
        if !matches!(
            collection.ty().kind(),
            TypeKind::Set(_) | TypeKind::Multiset(_) | TypeKind::Seq(_) | TypeKind::Map(..)
        ) {
            typecheck_error!("Length of non-collection type: {:?}", collection.ty(),);
        }
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::CollectionLen(collection.as_dyn())),
        ))
    }

    /// The domain (key set) of a native Viper `Map`.
    pub fn mk_map_domain_expr<'vir, Curr, Next>(
        &'vir self,
        map: ExprGenMap<'vir, Curr, Next>,
    ) -> ExprGenSet<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::MapDomain(map.as_dyn())),
        ))
    }

    /// The range (value set) of a native Viper `Map`.
    pub fn mk_map_range_expr<'vir, Curr, Next>(
        &'vir self,
        map: ExprGenMap<'vir, Curr, Next>,
    ) -> ExprGenSet<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::MapRange(map.as_dyn())),
        ))
    }

    /// To be used only when `kind` is generated e.g. with a `from` call.
    /// Otherwise always use either `mk_eq_expr` or `mk_bin_op_expr`.
    pub fn mk_bin_op_expr_inner<'vir, Curr, Next>(
        &'vir self,
        kind: BinOpKind,
        lhs: ExprGenDyn<'vir, Curr, Next>,
        rhs: ExprGenDyn<'vir, Curr, Next>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        if lhs.ty() != rhs.ty() {
            typecheck_error!(
                "Type mismatch in binary operation {:?}. LHS type: {:?}, RHS type: {:?}",
                kind,
                lhs.ty(),
                rhs.ty(),
            );
        }
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::BinOp(
            self.alloc(BinOpGenData { kind, lhs, rhs }),
        ))))
    }

    fn mk_collection_bin_op_expr_inner<'vir, Curr, Next>(
        &'vir self,
        kind: CollectionBinOpKind,
        lhs: ExprGenDyn<'vir, Curr, Next>,
        rhs: ExprGenDyn<'vir, Curr, Next>,
    ) -> ExprGenDyn<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::CollectionBinOp(self.alloc(CollectionBinOpGenData { kind, lhs, rhs })),
        )))
    }

    pub fn mk_field_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        recv: ExprGenRef<'vir, Curr, Next>,
        field: Field<'vir, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Field(recv, field.as_dyn())),
        ))
    }

    pub(crate) fn mk_adt_destructor_expr<'vir, Curr, Next, T: CompType, R: CompType>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next, T>,
        destr: AdtDestructor<'vir, T, R>,
    ) -> ExprGen<'vir, Curr, Next, R> {
        if recv.ty() != destr.input {
            typecheck_error!(
                "Unexpected type for adt field {}. Expected: {:?}, Actual: {:?}",
                destr.name,
                destr.input,
                recv.ty()
            );
        }
        self.alloc(ExprGenData::new(self.alloc(
            ExprKindGenData::AdtDestructor(recv.as_dyn(), destr.as_dyn()),
        )))
    }

    pub fn mk_adt_discriminator_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        recv: ExprGen<'vir, Curr, Next, T>,
        discr: &'vir str,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::AdtDiscriminator(recv.as_dyn(), discr)),
        ))
    }

    pub fn mk_unfolding_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        target: PredicateAppGen<'vir, Curr, Next>,
        expr: ExprGen<'vir, Curr, Next, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::Unfolding(
            self.alloc(UnfoldingGenData {
                target,
                expr: expr.as_dyn(),
            }),
        ))))
    }

    pub fn mk_acc_field_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        recv: ExprGenRef<'vir, Curr, Next>,
        field: Field<'vir, T>,
        perm: Option<ExprGenPerm<'vir, Curr, Next>>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::AccField(
            self.alloc(AccFieldGenData {
                recv,
                field: field.as_dyn(),
                perm,
            }),
        ))))
    }

    pub fn mk_const_expr<'vir, Curr, Next>(
        &'vir self,
        value: ConstData,
    ) -> ExprGenPrim<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Const(self.alloc(value))),
        ))
    }

    pub fn mk_inhale_exhale_expr<'vir, Curr, Next>(
        &'vir self,
        inhale: ExprGenBool<'vir, Curr, Next>,
        exhale: ExprGenBool<'vir, Curr, Next>,
    ) -> ExprGenBool<'vir, Curr, Next> {
        self.alloc(ExprGenData::new(self.alloc(ExprKindGenData::InhaleExhale(
            self.alloc(InhaleExhaleGenData { inhale, exhale }),
        ))))
    }

    pub fn mk_todo_expr<'vir, Curr, Next, T: CompType>(
        &'vir self,
        msg: &'vir str,
        ty: Type<'vir, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new_with_ty(
            self.alloc(ExprKindGenData::Todo(msg)),
            ty,
        ))
    }

    pub fn mk_result<'vir, Curr, Next, T: CompType>(
        &'vir self,
        ty: Type<'vir, T>,
    ) -> ExprGen<'vir, Curr, Next, T> {
        self.alloc(ExprGenData::new(
            self.alloc(ExprKindGenData::Result(ty.as_dyn())),
        ))
    }

    pub fn mk_field<'vir, T: CompType>(
        &'vir self,
        name: &'vir str,
        ty: Type<'vir, T>,
    ) -> Field<'vir, T> {
        self.alloc(FieldData { name, ty })
    }

    pub fn mk_adt_destructor<'vir, T: CompType, R: CompType>(
        &'vir self,
        name: &'vir str,
        input: Type<'vir, T>,
        ty: Type<'vir, R>,
    ) -> AdtDestructor<'vir, T, R> {
        self.alloc(AdtDestructorData { name, input, ty })
    }

    pub fn mk_domain_axiom<'vir, Curr, Next>(
        &'vir self,
        name: ViperIdent<'vir>,
        expr: ExprGenBool<'vir, Curr, Next>,
    ) -> DomainAxiomGen<'vir, Curr, Next> {
        self.alloc(DomainAxiomGenData {
            name: name.to_str(),
            expr,
        })
    }

    pub fn mk_domain_axiom_inverse<'vir, T: CompType, U: CompType>(
        &'vir self,
        a: FunctionIdn<'vir, T, U>,
        b: FunctionIdn<'vir, U, T>,
    ) -> DomainAxiomGen<'vir, (), !> {
        let val = self.mk_local_decl("val", b.arity().ty());
        let val_ex = self.mk_local_ex(val);
        let inner = b(val_ex);
        let expr = self.mk_forall_expr(
            self.alloc_slice(&[val]),
            self.alloc_slice(&[self.mk_trigger(self.alloc_slice(&[inner]))]),
            self.mk_eq_expr(a(inner), val_ex),
        );
        self.alloc(DomainAxiomGenData {
            name: self.alloc_str(&format!("ax_inverse_{}_{}", a.name(), b.name(),)),
            expr,
        })
    }

    pub fn mk_domain_function<'vir, A: Arity>(
        &'vir self,
        ident: FunctionIdn<'vir, A, impl CompType>,
        unique: bool,
        interpretation: Option<&'vir str>,
    ) -> DomainFunction<'vir> {
        let params = A::params(ident.arity());
        self.alloc(DomainFunctionData {
            unique,
            name: ident.name(),
            args: self.alloc_slice(params.as_slice()),
            ret: ident.result().as_dyn(),
            interpretation: interpretation.map(|i| InterpretationData { interpretation: i }),
        })
    }

    pub fn mk_function<'vir, Curr, Next, A: Arity, T: CompType>(
        &'vir self,
        ident: FunctionIdn<'vir, A, T>,
        args: A::Locals<'_, 'vir>,
        pres: &'vir [ExprGenBool<'vir, Curr, Next>],
        posts: &'vir [ExprGenBool<'vir, Curr, Next>],
        decreases: Option<DecreasesGen<'vir, Curr, Next>>,
        expr: Option<ExprGen<'vir, Curr, Next, T>>,
    ) -> FunctionGen<'vir, Curr, Next> {
        let name = ident.name().to_str();
        let ret = ident.result();
        let args = A::locals(self, args);
        // TODO: Typecheck pre and post conditions
        if let Some(body) = expr {
            if body.ty() != ret {
                typecheck_error!(
                    "Function {} has inconsistent return type. Expected: {:?}, Actual: {:?}",
                    name,
                    ret,
                    body.ty()
                );
            }
            cfg_if! {
                if #[cfg(debug_assertions)] {
                    let mut m = HashMap::new();
                    for arg in args {
                        m.insert(arg.name, arg.ty_dyn());
                    }
                    check_expr_bindings(&mut m, body.as_dyn());
                }
            }
        }
        self.alloc(FunctionGenData {
            name,
            args,
            ret: ret.as_dyn(),
            pres,
            posts,
            decreases: decreases.unwrap_or(&DecreasesGenData::None),
            expr: expr.map(|e| e.as_dyn()),
        })
    }

    pub fn mk_predicate<'vir, Curr, Next, A: Arity + Debug>(
        &'vir self,
        ident: PredicateIdn<'vir, A>,
        args: A::Locals<'_, 'vir>,
        expr: Option<ExprGenBool<'vir, Curr, Next>>,
    ) -> PredicateGen<'vir, Curr, Next> {
        let args = A::locals(self, args);
        A::types_match(ident.arity(), args, ident.debug_info());
        self.mk_predicate_unchecked(ident.name().to_str(), args, expr)
    }

    pub fn mk_predicate_unchecked<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDeclDyn<'vir>],
        expr: Option<ExprGenBool<'vir, Curr, Next>>,
    ) -> PredicateGen<'vir, Curr, Next> {
        self.alloc(PredicateGenData { name, args, expr })
    }

    pub fn mk_adt<'vir, Curr, Next>(
        &'vir self,
        name: ViperIdent<'vir>,
        typarams: &'vir [DomainParam<'vir>],
        constructors: &'vir [AdtConstructorGen<'vir, Curr, Next>],
    ) -> AdtGen<'vir, Curr, Next> {
        self.alloc(AdtGenData {
            name: name.to_str(),
            typarams,
            constructors,
        })
    }

    pub fn mk_adt_constructor<'vir, Curr, Next, T: CompType>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDecl<'vir, T>],
        // TODO: axiom support
    ) -> AdtConstructorGen<'vir, Curr, Next> {
        self.alloc(AdtConstructorGenData {
            name,
            args: args.as_dyn(),
            axiom: None,
        })
    }

    pub fn mk_domain<'vir, Curr, Next>(
        &'vir self,
        name: ViperIdent<'vir>,
        typarams: &'vir [DomainParam<'vir>],
        axioms: &'vir [DomainAxiomGen<'vir, Curr, Next>],
        functions: &'vir [DomainFunction<'vir>],
        interpretation: Option<&'vir [&'vir BackendInterpretationPair]>,
    ) -> DomainGen<'vir, Curr, Next> {
        assert_eq!(typarams.len(), 0, "Domain type parameters are not yet supported (because `FunctionIdn` doesn't have a mechanism to add a type_map for calls)");
        self.alloc(DomainGenData {
            name: name.to_str(),
            typarams,
            axioms,
            functions,
            interpretation: interpretation
                .map(|i| self.alloc(BackendInterpretationData { interpretation: i })),
        })
    }

    pub fn mk_exhale_stmt<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGenBool<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Exhale(expr).alloc_vcx(self)
    }

    pub fn mk_unfold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Unfold(pred_app).alloc_vcx(self)
    }

    pub fn mk_fold_stmt<'vir, Curr, Next>(
        &'vir self,
        pred_app: PredicateAppGen<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Fold(pred_app).alloc_vcx(self)
    }

    pub fn mk_package_stmt<'vir, Curr, Next>(
        &'vir self,
        wand: WandGen<'vir, Curr, Next>,
        stmts: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Package(wand, stmts).alloc_vcx(self)
    }

    pub fn mk_apply_stmt<'vir, Curr, Next>(
        &'vir self,
        wand: WandGen<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Apply(wand).alloc_vcx(self)
    }

    pub fn mk_pure_assign_stmt<'vir, Curr, Next, T: CompType>(
        &'vir self,
        lhs: ExprGen<'vir, Curr, Next, T>,
        rhs: ExprGen<'vir, Curr, Next, T>,
    ) -> StmtGen<'vir, Curr, Next> {
        if lhs.ty() != rhs.ty() {
            typecheck_error!(
                "Pure assign statement requires lhs and rhs to have the same type. lhs: {:?}, rhs: {:?}",
                lhs.ty(),
                rhs.ty()
            );
        }
        StmtKindGenData::PureAssign(self.alloc(PureAssignGenData {
            lhs: lhs.as_dyn(),
            rhs: rhs.as_dyn(),
        }))
        .alloc_vcx(self)
    }

    pub fn mk_local_decl_stmt<'vir, Curr, Next, T: CompType>(
        &'vir self,
        local: LocalDecl<'vir, T>,
        expr: Option<ExprGen<'vir, Curr, Next, T>>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::LocalDecl(local.as_dyn(), expr.map(|e| e.as_dyn())).alloc_vcx(self)
    }

    pub fn mk_if_stmt<'vir, Curr, Next>(
        &'vir self,
        cond: ExprGenBool<'vir, Curr, Next>,
        then_stmts: &'vir [StmtGen<'vir, Curr, Next>],
        else_stmts: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::If(cond, then_stmts, else_stmts).alloc_vcx(self)
    }

    pub fn mk_block_label<'vir>(
        &'vir self,
        block: usize,
        pres: impl IntoIterator<Item = usize>,
    ) -> CfgBlockLabel<'vir> {
        let pres = self.alloc(pres.into_iter().map(|l| self.alloc(l)).collect::<Vec<_>>());
        if pres.is_empty() {
            self.alloc(CfgBlockLabelData::BasicBlock(block))
        } else {
            self.alloc(CfgBlockLabelData::PreLoopBasicBlock(block, pres))
        }
    }

    pub fn mk_terminator_label<'vir>(
        &'vir self,
        block: usize,
        pres: impl IntoIterator<Item = usize>,
    ) -> CfgBlockLabel<'vir> {
        let pres = self.alloc(pres.into_iter().map(|l| self.alloc(l)).collect::<Vec<_>>());
        if pres.is_empty() {
            self.alloc(CfgBlockLabelData::BasicBlockTerminator(block))
        } else {
            self.alloc(CfgBlockLabelData::PreLoopBasicBlockTerminator(block, pres))
        }
    }

    pub fn mk_label_stmt<'vir, Curr, Next>(
        &'vir self,
        label: &'vir str,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Label(label).alloc_vcx(self)
    }

    pub fn mk_inhale_stmt<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGenBool<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Inhale(expr).alloc_vcx(self)
    }

    pub fn mk_refute_stmt<'vir, Curr, Next>(
        &'vir self,
        expr: ExprGenBool<'vir, Curr, Next>,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Refute(expr).alloc_vcx(self)
    }

    pub fn mk_assume_false_stmt<'vir, Curr, Next>(
        &'vir self,
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(TerminatorStmtGenData::AssumeFalse)
    }

    pub fn mk_goto_stmt<'vir, Curr, Next>(
        &'vir self,
        block: CfgBlockLabel<'vir>,
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(TerminatorStmtGenData::Goto(block))
    }

    pub fn mk_dummy_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str,
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(TerminatorStmtGenData::Dummy(msg))
    }

    pub fn mk_comment_stmt<'vir, Curr, Next>(
        &'vir self,
        msg: &'vir str,
    ) -> StmtGen<'vir, Curr, Next> {
        StmtKindGenData::Comment(msg).alloc_vcx(self)
    }

    pub fn mk_goto_if_stmt<'vir, Curr, Next>(
        &'vir self,
        value: ExprGenDyn<'vir, Curr, Next>,
        targets: &'vir [GotoIfTargetGen<'vir, Curr, Next>],
        otherwise: CfgBlockLabel<'vir>,
        otherwise_statements: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> TerminatorStmtGen<'vir, Curr, Next> {
        self.alloc(TerminatorStmtGenData::GotoIf(self.alloc(GotoIfGenData {
            value,
            targets,
            otherwise,
            otherwise_statements,
        })))
    }

    pub fn mk_goto_if_target<'vir, Curr, Next>(
        &'vir self,
        value: ExprGenDyn<'vir, Curr, Next>,
        label: CfgBlockLabel<'vir>,
        statements: &'vir [StmtGen<'vir, Curr, Next>],
    ) -> GotoIfTargetGen<'vir, Curr, Next> {
        self.alloc(GotoIfTargetGenData {
            value,
            label,
            statements,
        })
    }

    pub fn mk_cfg_block<'vir, Curr, Next>(
        &'vir self,
        label: CfgBlockLabel<'vir>,
        invariants: &'vir [ExprGenBool<'vir, Curr, Next>],
        stmts: &'vir [StmtGen<'vir, Curr, Next>],
        terminator: TerminatorStmtGen<'vir, Curr, Next>,
    ) -> CfgBlockGen<'vir, Curr, Next> {
        let label = self.alloc(CfgLabelGenData { label, invariants });
        self.alloc(CfgBlockGenData {
            label,
            stmts,
            terminator,
        })
    }

    pub fn mk_method<'vir, Curr, Next, A: Arity>(
        &'vir self,
        ident: MethodIdn<'vir, A>,
        args: A::Locals<'_, 'vir>,
        rets: &'vir [LocalDeclDyn<'vir>],
        pres: &'vir [ExprGenBool<'vir, Curr, Next>],
        posts: &'vir [ExprGenBool<'vir, Curr, Next>],
        blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
    ) -> MethodGen<'vir, Curr, Next> {
        let args = A::locals(self, args);
        A::types_match(ident.arity(), args, ident.debug_info());
        self.mk_method_unchecked(ident.name().to_str(), args, rets, pres, posts, blocks)
    }

    pub fn mk_method_unchecked<'vir, Curr, Next>(
        &'vir self,
        name: &'vir str,
        args: &'vir [LocalDeclDyn<'vir>],
        rets: &'vir [LocalDeclDyn<'vir>],
        pres: &'vir [ExprGenBool<'vir, Curr, Next>],
        posts: &'vir [ExprGenBool<'vir, Curr, Next>],
        blocks: Option<&'vir [CfgBlockGen<'vir, Curr, Next>]>, // first one is the entrypoint
    ) -> MethodGen<'vir, Curr, Next> {
        cfg_if! {
            if #[cfg(debug_assertions)] {
                if let Some(blocks) = blocks {
                    let mut m = HashMap::new();
                    for arg in args {
                        m.insert(arg.name, arg.ty_dyn());
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
            body: blocks.map(|blocks| self.alloc(MethodBodyGenData { blocks })),
        })
    }

    pub fn mk_program<'vir, Curr, Next>(
        &'vir self,
        fields: &'vir [FieldDyn<'vir>],
        adts: &'vir [AdtGen<'vir, Curr, Next>],
        domains: &'vir [DomainGen<'vir, Curr, Next>],
        predicates: &'vir [PredicateGen<'vir, Curr, Next>],
        functions: &'vir [FunctionGen<'vir, Curr, Next>],
        methods: &'vir [MethodGen<'vir, Curr, Next>],
    ) -> ProgramGen<'vir, Curr, Next> {
        self.alloc(ProgramGenData {
            fields,
            adts,
            domains,
            predicates,
            functions,
            methods,
        })
    }

    /// Combines `elems` as a balanced tree rather than a linear fold. This
    /// keeps the AST depth logarithmic, otherwise deep chains would overflow
    /// the stack of recursive consumers (serde, `ToViper`).
    fn mk_assoc_op<'vir, Curr, Next, T: CompType>(
        &'vir self,
        kind: BinOpKind,
        default: Option<ExprGen<'vir, Curr, Next, T>>,
        elems: &[ExprGen<'vir, Curr, Next, T>],
    ) -> ExprGen<'vir, Curr, Next, T>
    where
        crate::Prim: crate::TransmuteFrom<T>,
    {
        match elems {
            [] => default.unwrap(),
            [e] => e,
            _ => {
                let (left, right) = elems.split_at(elems.len() / 2);
                let lhs = self.mk_assoc_op(kind, None, left);
                let rhs = self.mk_assoc_op(kind, None, right);
                self.mk_bin_op_expr(kind, lhs, rhs).downcast_ty()
            }
        }
    }

    pub fn mk_conj<'vir, Curr, Next>(
        &'vir self,
        elems: &[ExprGenBool<'vir, Curr, Next>],
    ) -> ExprGenBool<'vir, Curr, Next> {
        let default = Some(self.mk_bool::<true>().lazy());
        self.mk_assoc_op(BinOpKind::And, default, elems)
    }

    pub fn mk_disj<'vir, Curr, Next>(
        &'vir self,
        elems: &[ExprGenBool<'vir, Curr, Next>],
    ) -> ExprGenBool<'vir, Curr, Next> {
        let default = Some(self.mk_bool::<false>().lazy());
        self.mk_assoc_op(BinOpKind::Or, default, elems)
    }

    pub const fn get_int_data(rust_ty: &ty::TyKind) -> (u32, bool) {
        match rust_ty {
            ty::Int(ty::IntTy::Isize) => ((std::mem::size_of::<isize>() * 8) as u32, true),
            ty::Int(ty::IntTy::I8) => (8, true),
            ty::Int(ty::IntTy::I16) => (16, true),
            ty::Int(ty::IntTy::I32) => (32, true),
            ty::Int(ty::IntTy::I64) => (64, true),
            ty::Int(ty::IntTy::I128) => (128, true),
            ty::Uint(ty::UintTy::Usize) => ((std::mem::size_of::<usize>() * 8) as u32, false),
            ty::Uint(ty::UintTy::U8) => (8, false),
            ty::Uint(ty::UintTy::U16) => (16, false),
            ty::Uint(ty::UintTy::U32) => (32, false),
            ty::Uint(ty::UintTy::U64) => (64, false),
            ty::Uint(ty::UintTy::U128) => (128, false),
            // See https://doc.rust-lang.org/book/ch03-02-data-types.html#the-character-type
            ty::Char => (32, false),
            _ => unreachable!(),
        }
    }
    pub const fn get_min_int<'vir>(&'vir self, rust_ty: &ty::TyKind) -> ExprInt<'vir> {
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
    pub const fn get_max_int<'vir>(&'vir self, rust_ty: &ty::TyKind) -> ExprInt<'vir> {
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
    pub fn get_modulo_int<'vir>(&'vir self, rust_ty: &ty::TyKind) -> ExprInt<'vir> {
        match Self::get_int_data(rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ 1_u128 << u8::BITS }>(),
            (u16::BITS, _) => self.mk_uint::<{ 1_u128 << u16::BITS }>(),
            (u32::BITS, _) => self.mk_uint::<{ 1_u128 << u32::BITS }>(),
            (u64::BITS, _) => self.mk_uint::<{ 1_u128 << u64::BITS }>(),
            (u128::BITS, _) => {
                // `2^128` overflows `u128` and can't be written as a literal, so
                // build it as `2^127 + 2^127` in the (unbounded) Viper `Int`.
                // TODO: make this a `const` once `Expr` isn't invariant in `'vir` so that it can be `'const` instead
                let half = self.mk_uint::<{ 1_u128 << (u128::BITS - 1) }>();
                self.mk_bin_op_expr(BinOpKind::Add, half.as_dyn(), half.as_dyn())
                    .downcast_ty()
            }
            _ => unreachable!(),
        }
    }
    pub fn get_signed_shift_int<'vir>(&'vir self, rust_ty: &ty::TyKind) -> Option<ExprInt<'vir>> {
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
    pub fn get_bit_width_int<'vir>(&'vir self, rust_ty: &ty::TyKind) -> ExprInt<'vir> {
        match Self::get_int_data(rust_ty) {
            (u8::BITS, _) => self.mk_uint::<{ u8::BITS as u128 }>(),
            (u16::BITS, _) => self.mk_uint::<{ u16::BITS as u128 }>(),
            (u32::BITS, _) => self.mk_uint::<{ u32::BITS as u128 }>(),
            (u64::BITS, _) => self.mk_uint::<{ u64::BITS as u128 }>(),
            (u128::BITS, _) => self.mk_uint::<{ u128::BITS as u128 }>(),
            _ => unreachable!(),
        }
    }
    /// Wrap `exp` into the range of the integer type `rust_ty` (two's complement):
    /// a `uN` target is `exp mod 2^N`; an `iN` target is
    /// `((exp + 2^(N-1)) mod 2^N) - 2^(N-1)`. This is the identity when `exp` is
    /// already in range, and reproduces Rust's `as`/wrapping-arithmetic otherwise.
    pub fn get_wrapped_val<'vir>(
        &'vir self,
        mut exp: ExprInt<'vir>,
        rust_ty: &ty::TyKind,
    ) -> ExprInt<'vir> {
        let shift_amount = self.get_signed_shift_int(rust_ty);
        if let Some(half) = shift_amount {
            exp = self.mk_bin_op_expr(BinOpKind::Add, exp, half).downcast_ty();
        }
        let modulo_val = self.get_modulo_int(rust_ty);
        exp = self
            .mk_bin_op_expr(BinOpKind::Mod, exp, modulo_val)
            .downcast_ty();
        if let Some(half) = shift_amount {
            exp = self.mk_bin_op_expr(BinOpKind::Sub, exp, half).downcast_ty();
        }
        exp
    }
}
