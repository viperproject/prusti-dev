//! Peephole simplification of hole-free expressions, run over the final
//! program (functions and methods only; folding in domain axioms could remove
//! the terms that quantifier triggers rely on).
//!
//! The rules undo the wrap/unwrap round-trips produced by composing
//! independently encoded snapshot operations (reference snapshots built and
//! immediately dereferenced, generic casts cancelled out, snapshot
//! constructors compared field by field). All rules are local equivalences:
//!  - an adt field read of the matching constructor application yields the
//!    constructor argument,
//!  - `C(xs..) == C(ys..)` for an adt constructor `C` is the conjunction of
//!    the pairwise argument equalities (adt constructors are injective),
//!  - `let x = v in b` is dropped when `x` is unused, and inlined when `v` is
//!    a local/constant or `x` is used exactly once.
//!
//! Constructors and destructors are recognized via the program's adt
//! declarations ([`AdtIndex`]), which also ground the injectivity the
//! equality rule relies on. The generic casts are such a pair, with
//! `make_generic_X` a constructor of `s_Param` and `make_concrete_X` the
//! destructor of its value field, so `make_concrete_X(make_generic_X(e))`
//! folds to `e`. The other direction, `make_generic_X(make_concrete_X(p))`,
//! is left standing: it needs to know that `p` really inhabits `X`.
//!
//! Inlining a binding (or splicing a constructor argument at a use site)
//! moves the bound expression to the use site, which is only sound while the
//! heap state is unchanged: the environment is emptied of heap-dependent
//! entries when descending into `old(..)`. Occurrences inside `old(..)`,
//! inside triggers, or under a binder capturing a local of the bound
//! expression block inlining. Substituting a binding whose value is a local
//! is not checked for capture by nested `let`s: the pass relies on the
//! encoder never reusing a `let` name within its scope (the pure encoding
//! versions every name and prefixes it with its nesting depth).
//!
//! Magic wands (and their `package`/`apply` statements) are left entirely
//! untouched: Viper matches packaged wand instances syntactically, so a wand
//! must keep its exact encoded shape everywhere it is mentioned.

use std::collections::{HashMap, HashSet};

use crate::{data::*, gendata::*, genrefs::*, refs::*, CastType, VirCtxt};

/// The program's adt constructors and destructors, used to recognize the
/// foldable applications.
pub struct AdtIndex<'vir> {
    /// Constructor name to its ordered field (destructor) declarations.
    constructors: HashMap<&'vir str, &'vir [crate::LocalDeclDyn<'vir>]>,
    /// Destructor name to its constructor's name and field index.
    destructors: HashMap<&'vir str, (&'vir str, usize)>,
}

impl<'vir> AdtIndex<'vir> {
    pub fn new(adts: &[Adt<'vir>]) -> Self {
        let mut constructors = HashMap::new();
        let mut destructors = HashMap::new();
        for adt in adts {
            for cons in adt.constructors {
                constructors.insert(cons.name, cons.args);
                for (idx, field) in cons.args.iter().enumerate() {
                    destructors.insert(field.name, (cons.name, idx));
                }
            }
        }
        Self {
            constructors,
            destructors,
        }
    }
}

pub fn function<'vir, 'tcx>(
    vcx: &'vir VirCtxt<'tcx>,
    adts: &AdtIndex<'vir>,
    f: Function<'vir>,
) -> Function<'vir> {
    let mut s = Simplifier::new(vcx, adts);
    vcx.alloc(FunctionGenData {
        name: f.name,
        args: f.args,
        ret: f.ret,
        pres: s.roots(f.pres),
        posts: s.roots(f.posts),
        decreases: s.decreases(f.decreases),
        expr: s.opt_root(f.expr),
    })
}

pub fn method<'vir, 'tcx>(
    vcx: &'vir VirCtxt<'tcx>,
    adts: &AdtIndex<'vir>,
    m: Method<'vir>,
) -> Method<'vir> {
    let mut s = Simplifier::new(vcx, adts);
    vcx.alloc(MethodGenData {
        name: m.name,
        args: m.args,
        rets: m.rets,
        pres: s.roots(m.pres),
        posts: s.roots(m.posts),
        body: m.body.map(|body| {
            let blocks = body.blocks.iter().map(|b| s.block(b)).collect::<Vec<_>>();
            vcx.alloc(MethodBodyGenData {
                blocks: vcx.alloc_slice(&blocks),
            })
        }),
    })
}

/// A `let`-bound value in scope. `subst` entries are substituted at every
/// (non-trigger) use site; the others are only used to resolve locals when
/// matching the patterns above.
#[derive(Clone, Copy)]
struct Binding<'vir> {
    val: ExprDyn<'vir>,
    subst: bool,
}

struct Simplifier<'enc, 'vir, 'tcx> {
    vcx: &'vir VirCtxt<'tcx>,
    adts: &'enc AdtIndex<'vir>,
    env: HashMap<&'vir str, Binding<'vir>>,
}

impl<'enc, 'vir, 'tcx> Simplifier<'enc, 'vir, 'tcx> {
    fn new(vcx: &'vir VirCtxt<'tcx>, adts: &'enc AdtIndex<'vir>) -> Self {
        Self {
            vcx,
            adts,
            env: HashMap::new(),
        }
    }

    /// Rebuilds `orig` with a new kind, keeping its span and type.
    fn mk(&self, orig: ExprDyn<'vir>, kind: ExprKind<'vir>) -> ExprDyn<'vir> {
        self.vcx.alloc(ExprGenData::new_inner(
            kind,
            orig.debug_info,
            orig.span,
            orig.ty(),
        ))
    }

    fn expr_t<T: crate::CompType>(&mut self, e: Expr<'vir, T>) -> Expr<'vir, T> {
        self.expr(e.as_dyn()).inner_cast_ty()
    }

    fn exprs<T: crate::CompType>(&mut self, es: &'vir [Expr<'vir, T>]) -> &'vir [Expr<'vir, T>] {
        let out = es.iter().map(|e| self.expr_t(*e)).collect::<Vec<_>>();
        self.vcx.alloc_slice(&out)
    }

    fn opt_expr_t<T: crate::CompType>(
        &mut self,
        e: Option<Expr<'vir, T>>,
    ) -> Option<Expr<'vir, T>> {
        e.map(|e| self.expr_t(e))
    }

    /// Simplifies the root of an expression tree (a contract clause,
    /// invariant, body or statement operand), keeping the root's span. Viper
    /// blames e.g. a failing postcondition on the clause's root node, and
    /// the error handler is registered on the span of that node only (see
    /// `realloc_span`); a rule replacing the root by a subexpression would
    /// make the error impossible to backtranslate.
    fn root<T: crate::CompType>(&mut self, e: Expr<'vir, T>) -> Expr<'vir, T> {
        let simplified = self.expr(e.as_dyn());
        if std::ptr::eq(simplified, e.as_dyn()) {
            return e;
        }
        // A root without a span has no handler; keep the result's own.
        if e.span.is_none() {
            return simplified.inner_cast_ty();
        }
        self.vcx
            .alloc(ExprGenData::new_inner(
                simplified.kind,
                simplified.debug_info,
                e.span,
                simplified.ty(),
            ))
            .inner_cast_ty()
    }

    fn roots<T: crate::CompType>(&mut self, es: &'vir [Expr<'vir, T>]) -> &'vir [Expr<'vir, T>] {
        let out = es.iter().map(|e| self.root(*e)).collect::<Vec<_>>();
        self.vcx.alloc_slice(&out)
    }

    fn opt_root<T: crate::CompType>(&mut self, e: Option<Expr<'vir, T>>) -> Option<Expr<'vir, T>> {
        e.map(|e| self.root(e))
    }

    fn decreases(
        &mut self,
        d: &'vir DecreasesGenData<'vir, (), !>,
    ) -> &'vir DecreasesGenData<'vir, (), !> {
        match d {
            DecreasesGenData::None | DecreasesGenData::Star => d,
            DecreasesGenData::Tuple(es, cond) => {
                let es = self.roots(es);
                let cond = self.opt_root(*cond);
                self.vcx.alloc(DecreasesGenData::Tuple(es, cond))
            }
            DecreasesGenData::Wildcard(cond) => {
                let cond = self.opt_root(*cond);
                self.vcx.alloc(DecreasesGenData::Wildcard(cond))
            }
        }
    }

    fn expr(&mut self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        match e.kind {
            ExprKindGenData::Local(local) => match self.env.get(local.name) {
                // The bound value is already simplified in its own scope;
                // do not re-process it (its locals refer to outer bindings).
                Some(b) if b.subst => b.val,
                _ => e,
            },
            ExprKindGenData::Const(_)
            | ExprKindGenData::Result(_)
            | ExprKindGenData::Lazy(_)
            | ExprKindGenData::Todo(_) => e,
            ExprKindGenData::Field(recv, field) => {
                let recv2 = self.expr(recv.as_dyn());
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::Field(recv2.inner_cast_ty(), field)),
                )
            }
            ExprKindGenData::Old(o) => {
                // Only heap-independent bindings survive into `old(..)`.
                let saved = self.env.clone();
                self.env.retain(|_, b| {
                    matches!(
                        b.val.kind,
                        ExprKindGenData::Local(_) | ExprKindGenData::Const(_)
                    )
                });
                let inner = self.expr(o.expr);
                self.env = saved;
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::Old(self.vcx.alloc(OldGenData {
                            expr: inner,
                            label: o.label,
                        }))),
                )
            }
            ExprKindGenData::AccField(a) => {
                let recv = self.expr(a.recv.as_dyn());
                let perm = self.opt_expr_t(a.perm);
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::AccField(self.vcx.alloc(AccFieldGenData {
                            recv: recv.inner_cast_ty(),
                            field: a.field,
                            perm,
                        }))),
                )
            }
            ExprKindGenData::Unfolding(u) => {
                let target = self.predicate_app(u.target);
                let inner = self.expr(u.expr);
                self.mk(
                    e,
                    self.vcx.alloc(ExprKindGenData::Unfolding(self.vcx.alloc(
                        UnfoldingGenData {
                            target,
                            expr: inner,
                        },
                    ))),
                )
            }
            ExprKindGenData::UnOp(u) => {
                let inner = self.expr(u.expr.as_dyn());
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
                            kind: u.kind,
                            expr: inner.inner_cast_ty(),
                        }))),
                )
            }
            ExprKindGenData::BinOp(b) => {
                let lhs = self.expr(b.lhs);
                let rhs = self.expr(b.rhs);
                match b.kind {
                    BinOpKind::CmpEq => {
                        if let Some(eq) = self.fold_eq(e, lhs, rhs) {
                            return eq;
                        }
                    }
                    BinOpKind::CmpNe => {
                        if let Some(eq) = self.fold_eq(e, lhs, rhs) {
                            return self.mk(
                                e,
                                self.vcx.alloc(ExprKindGenData::UnOp(self.vcx.alloc(
                                    UnOpGenData {
                                        kind: UnOpKind::Not,
                                        expr: eq.inner_cast_ty(),
                                    },
                                ))),
                            );
                        }
                    }
                    _ => (),
                }
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                            kind: b.kind,
                            lhs,
                            rhs,
                        }))),
                )
            }
            ExprKindGenData::CollectionBinOp(b) => {
                let lhs = self.expr(b.lhs);
                let rhs = self.expr(b.rhs);
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::CollectionBinOp(self.vcx.alloc(
                            CollectionBinOpGenData {
                                kind: b.kind,
                                lhs,
                                rhs,
                            },
                        ))),
                )
            }
            ExprKindGenData::CollectionLiteral(l) => {
                let values = self.exprs(l.values);
                self.mk(
                    e,
                    self.vcx.alloc(ExprKindGenData::CollectionLiteral(
                        self.vcx
                            .alloc(CollectionLiteralGenData { values, ty: l.ty }),
                    )),
                )
            }
            ExprKindGenData::CollectionUpdate(u) => {
                let target = self.expr(u.target);
                let key = self.expr(u.key);
                let val = self.expr(u.val);
                self.mk(
                    e,
                    self.vcx.alloc(ExprKindGenData::CollectionUpdate(
                        self.vcx.alloc(CollectionUpdateGenData { target, key, val }),
                    )),
                )
            }
            ExprKindGenData::CollectionLen(inner) => {
                let inner = self.expr(inner);
                self.mk(e, self.vcx.alloc(ExprKindGenData::CollectionLen(inner)))
            }
            ExprKindGenData::MapDomain(inner) => {
                let inner = self.expr(inner);
                self.mk(e, self.vcx.alloc(ExprKindGenData::MapDomain(inner)))
            }
            ExprKindGenData::MapRange(inner) => {
                let inner = self.expr(inner);
                self.mk(e, self.vcx.alloc(ExprKindGenData::MapRange(inner)))
            }
            ExprKindGenData::Ternary(t) => {
                let cond = self.expr(t.cond.as_dyn());
                if let ExprKindGenData::Const(ConstData::Bool(b)) = cond.kind {
                    return if *b {
                        self.expr(t.then)
                    } else {
                        self.expr(t.else_)
                    };
                }
                let then = self.expr(t.then);
                let else_ = self.expr(t.else_);
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
                            cond: cond.inner_cast_ty(),
                            then,
                            else_,
                        }))),
                )
            }
            ExprKindGenData::Forall(q) => {
                let saved = self.quantifier_env(q.qvars);
                let body = self.expr(q.body.as_dyn());
                self.env = saved;
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::Forall(self.vcx.alloc(ForallGenData {
                            qvars: q.qvars,
                            triggers: q.triggers,
                            body: body.inner_cast_ty(),
                        }))),
                )
            }
            ExprKindGenData::Exists(q) => {
                let saved = self.quantifier_env(q.qvars);
                let body = self.expr(q.body.as_dyn());
                self.env = saved;
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::Exists(self.vcx.alloc(ExistsGenData {
                            qvars: q.qvars,
                            triggers: q.triggers,
                            body: body.inner_cast_ty(),
                        }))),
                )
            }
            ExprKindGenData::Let(l) => self.let_expr(e, l),
            ExprKindGenData::FuncApp(app) => {
                let args = self.exprs(app.args);
                let app2 = self.vcx.alloc(FuncAppGenData {
                    target: app.target,
                    args,
                    result_ty: app.result_ty,
                    typ_var_map: app.typ_var_map,
                });
                self.mk(e, self.vcx.alloc(ExprKindGenData::FuncApp(app2)))
            }
            ExprKindGenData::PredicateApp(p) => {
                let p = self.predicate_app(p);
                self.mk(e, self.vcx.alloc(ExprKindGenData::PredicateApp(p)))
            }
            // Viper matches packaged magic-wand instances syntactically, so
            // wands must keep their exact encoded shape everywhere (see also
            // `Package`/`Apply` statements and the blocked count in
            // [`count_uses`]).
            ExprKindGenData::Wand(_) => e,
            ExprKindGenData::InhaleExhale(ie) => {
                let inhale = self.expr_t(ie.inhale);
                let exhale = self.expr_t(ie.exhale);
                self.mk(
                    e,
                    self.vcx.alloc(ExprKindGenData::InhaleExhale(
                        self.vcx.alloc(InhaleExhaleGenData { inhale, exhale }),
                    )),
                )
            }
            ExprKindGenData::AdtDestructor(recv, destr) => {
                let recv = self.expr(recv);
                if let Some(arg) = self.fold_destructor(recv, destr) {
                    return arg;
                }
                self.mk(
                    e,
                    self.vcx.alloc(ExprKindGenData::AdtDestructor(recv, destr)),
                )
            }
            ExprKindGenData::AdtDiscriminator(recv, name) => {
                let recv = self.expr(recv);
                self.mk(
                    e,
                    self.vcx
                        .alloc(ExprKindGenData::AdtDiscriminator(recv, name)),
                )
            }
        }
    }

    fn predicate_app(&mut self, p: PredicateAppGen<'vir, (), !>) -> PredicateAppGen<'vir, (), !> {
        let args = self.exprs(p.args);
        let perm = self.opt_expr_t(p.perm);
        self.vcx.alloc(PredicateAppGenData {
            target: p.target,
            args,
            perm,
        })
    }

    /// Saves the environment and drops the entries a quantifier invalidates:
    /// shadowed names and bindings whose locals the quantified variables
    /// would capture. This must match the capture rule of [`count_uses`]: a
    /// binding retained here is substituted in the body, so [`count_uses`]
    /// must count such occurrences as free, and vice versa.
    fn quantifier_env(
        &mut self,
        qvars: &'vir [crate::LocalDeclDyn<'vir>],
    ) -> HashMap<&'vir str, Binding<'vir>> {
        let saved = self.env.clone();
        self.env.retain(|name, b| {
            if qvars.iter().any(|q| q.name == *name) {
                return false;
            }
            let mut locals = HashSet::new();
            collect_locals(b.val, &mut locals);
            qvars.iter().all(|q| !locals.contains(q.name))
        });
        saved
    }

    fn let_expr(&mut self, e: ExprDyn<'vir>, l: &'vir LetGenData<'vir, (), !>) -> ExprDyn<'vir> {
        let val = self.expr(l.val);
        let trivial = matches!(
            val.kind,
            ExprKindGenData::Local(_) | ExprKindGenData::Const(_)
        );
        let prev = self.env.insert(
            l.name,
            Binding {
                val,
                subst: trivial,
            },
        );
        let body = self.expr(l.expr);
        self.restore(l.name, prev);

        let mut val_locals = HashSet::new();
        collect_locals(val, &mut val_locals);
        let mut uses = Uses::default();
        count_uses(l.name, &val_locals, body, false, &mut uses);
        if uses.free + uses.blocked == 0 {
            return body;
        }
        if uses.blocked == 0 && uses.free == 1 {
            let prev = self.env.insert(l.name, Binding { val, subst: true });
            let body = self.expr(body);
            self.restore(l.name, prev);
            return body;
        }
        self.mk(
            e,
            self.vcx
                .alloc(ExprKindGenData::Let(self.vcx.alloc(LetGenData {
                    name: l.name,
                    val,
                    expr: body,
                }))),
        )
    }

    fn restore(&mut self, name: &'vir str, prev: Option<Binding<'vir>>) {
        match prev {
            Some(b) => {
                self.env.insert(name, b);
            }
            None => {
                self.env.remove(name);
            }
        }
    }

    /// Follows locals to their bound values, for pattern matching only.
    fn resolve(&self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        let mut cur = e;
        while let ExprKindGenData::Local(l) = cur.kind {
            match self.env.get(l.name) {
                Some(b) => cur = b.val,
                None => break,
            }
        }
        cur
    }

    /// An adt field read of the matching constructor application yields the
    /// constructor argument.
    fn fold_destructor(
        &self,
        recv: ExprDyn<'vir>,
        destr: AdtDestructor<'vir, crate::Dyn, crate::Dyn>,
    ) -> Option<ExprDyn<'vir>> {
        let recv = self.resolve(recv);
        let ExprKindGenData::FuncApp(app) = recv.kind else {
            return None;
        };
        let (cons, idx) = *self.adts.destructors.get(destr.name)?;
        if app.target != cons {
            return None;
        }
        let arg = *app.args.get(idx)?;
        (recv.ty() == destr.input && arg.ty() == destr.ty).then_some(arg)
    }

    /// Simplified equality of two snapshots, if a rule applies: identical
    /// operands are `true`; applications of the same adt constructor compare
    /// pairwise (adt constructors are injective).
    fn fold_eq(
        &mut self,
        orig: ExprDyn<'vir>,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        if syntactic_eq(lhs, rhs) {
            return Some(self.vcx.mk_bool::<true>().as_dyn());
        }
        let (l, r) = (self.resolve(lhs), self.resolve(rhs));
        let (ExprKindGenData::FuncApp(la), ExprKindGenData::FuncApp(ra)) = (l.kind, r.kind) else {
            return None;
        };
        if la.target != ra.target
            || la.args.len() != ra.args.len()
            || !self.adts.constructors.contains_key(la.target)
        {
            return None;
        }
        if !la.args.iter().zip(ra.args).all(|(a, b)| a.ty() == b.ty()) {
            return None;
        }
        let eqs = la
            .args
            .iter()
            .zip(ra.args)
            .map(|(a, b)| self.mk_eq(orig, a, b))
            .collect::<Vec<_>>();
        Some(self.mk_and(eqs))
    }

    fn mk_eq(
        &mut self,
        orig: ExprDyn<'vir>,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        if let Some(eq) = self.fold_eq(orig, lhs, rhs) {
            return eq;
        }
        self.vcx.alloc(ExprGenData::new_inner(
            self.vcx
                .alloc(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                    kind: BinOpKind::CmpEq,
                    lhs,
                    rhs,
                }))),
            orig.debug_info,
            orig.span,
            crate::TYPE_BOOL.as_dyn(),
        ))
    }

    fn mk_and(&mut self, exprs: Vec<ExprDyn<'vir>>) -> ExprDyn<'vir> {
        let mut conjuncts = exprs
            .into_iter()
            .filter(|e| !matches!(e.kind, ExprKindGenData::Const(ConstData::Bool(true))));
        let Some(first) = conjuncts.next() else {
            return self.vcx.mk_bool::<true>().as_dyn();
        };
        conjuncts.fold(first, |acc, e| {
            self.vcx.alloc(ExprGenData::new_inner(
                self.vcx
                    .alloc(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                        kind: BinOpKind::And,
                        lhs: acc,
                        rhs: e,
                    }))),
                acc.debug_info,
                acc.span,
                crate::TYPE_BOOL.as_dyn(),
            ))
        })
    }

    // Statements (method bodies).

    fn block(&mut self, b: &'vir CfgBlockGenData<'vir, (), !>) -> CfgBlockGen<'vir, (), !> {
        let invariants = self.roots(b.label.invariants);
        let label = self.vcx.alloc(CfgLabelGenData {
            label: b.label.label,
            invariants,
        });
        let stmts = b.stmts.iter().map(|s| self.stmt(s)).collect::<Vec<_>>();
        let terminator = self.terminator(b.terminator);
        self.vcx.alloc(CfgBlockGenData {
            label,
            stmts: self.vcx.alloc_slice(&stmts),
            terminator,
        })
    }

    fn stmts(&mut self, stmts: &'vir [Stmt<'vir>]) -> &'vir [Stmt<'vir>] {
        let out = stmts.iter().map(|s| self.stmt(s)).collect::<Vec<_>>();
        self.vcx.alloc_slice(&out)
    }

    fn stmt(&mut self, s: Stmt<'vir>) -> Stmt<'vir> {
        let kind = match s.kind {
            StmtKindGenData::LocalDecl(decl, expr) => {
                let expr = self.opt_root(*expr);
                StmtKindGenData::LocalDecl(decl, expr)
            }
            StmtKindGenData::PureAssign(a) => {
                StmtKindGenData::PureAssign(self.vcx.alloc(PureAssignGenData {
                    lhs: self.root(a.lhs),
                    rhs: self.root(a.rhs),
                }))
            }
            StmtKindGenData::Inhale(e) => StmtKindGenData::Inhale(self.root(*e)),
            StmtKindGenData::Exhale(e) => StmtKindGenData::Exhale(self.root(*e)),
            StmtKindGenData::Assert(e) => StmtKindGenData::Assert(self.root(*e)),
            StmtKindGenData::Refute(e) => StmtKindGenData::Refute(self.root(*e)),
            StmtKindGenData::Unfold(p) => StmtKindGenData::Unfold(self.predicate_app(p)),
            StmtKindGenData::Fold(p) => StmtKindGenData::Fold(self.predicate_app(p)),
            // Wands (and their proof scripts) must keep their exact encoded
            // shape, see the `Wand` case in `expr`.
            StmtKindGenData::Package(..) | StmtKindGenData::Apply(_) => return s,
            StmtKindGenData::MethodCall(c) => {
                StmtKindGenData::MethodCall(self.vcx.alloc(MethodCallGenData {
                    targets: c.targets,
                    method: c.method,
                    args: self.roots(c.args),
                }))
            }
            StmtKindGenData::If(cond, then, else_) => {
                StmtKindGenData::If(self.root(*cond), self.stmts(then), self.stmts(else_))
            }
            StmtKindGenData::Label(_) | StmtKindGenData::Comment(_) | StmtKindGenData::Dummy(_) => {
                return s
            }
        };
        self.vcx.alloc(StmtGenData {
            kind: self.vcx.alloc(kind),
            span: s.span,
        })
    }

    fn terminator(
        &mut self,
        t: &'vir TerminatorStmtGenData<'vir, (), !>,
    ) -> TerminatorStmtGen<'vir, (), !> {
        match t {
            TerminatorStmtGenData::AssumeFalse
            | TerminatorStmtGenData::Goto(_)
            | TerminatorStmtGenData::Exit
            | TerminatorStmtGenData::Dummy(_) => t,
            TerminatorStmtGenData::GotoIf(g) => {
                let value = self.root(g.value);
                let targets = g
                    .targets
                    .iter()
                    .map(|t| {
                        self.vcx.alloc(GotoIfTargetGenData {
                            value: self.root(t.value),
                            label: t.label,
                            statements: self.stmts(t.statements),
                        }) as GotoIfTargetGen<'vir, (), !>
                    })
                    .collect::<Vec<_>>();
                let otherwise_statements = self.stmts(g.otherwise_statements);
                self.vcx.alloc(TerminatorStmtGenData::GotoIf(self.vcx.alloc(
                    GotoIfGenData {
                        value,
                        targets: self.vcx.alloc_slice(&targets),
                        otherwise: g.otherwise,
                        otherwise_statements,
                    },
                )))
            }
        }
    }
}

/// Syntactic equality, conservative (`false` for unhandled kinds). Used to
/// fold reflexive equalities.
fn syntactic_eq<'vir>(a: ExprDyn<'vir>, b: ExprDyn<'vir>) -> bool {
    if std::ptr::eq(a.kind, b.kind) {
        return true;
    }
    match (a.kind, b.kind) {
        (ExprKindGenData::Local(x), ExprKindGenData::Local(y)) => x.name == y.name,
        (ExprKindGenData::Const(x), ExprKindGenData::Const(y)) => x == y,
        (ExprKindGenData::FuncApp(x), ExprKindGenData::FuncApp(y)) => {
            x.target == y.target
                && x.args.len() == y.args.len()
                && x.args.iter().zip(y.args).all(|(a, b)| syntactic_eq(a, b))
        }
        (ExprKindGenData::AdtDestructor(e1, d1), ExprKindGenData::AdtDestructor(e2, d2)) => {
            d1.name == d2.name && syntactic_eq(e1, e2)
        }
        _ => false,
    }
}

#[derive(Default)]
struct Uses {
    free: usize,
    blocked: usize,
}

/// Counts the uses of `name` in `e`. Occurrences inside `old(..)`, inside
/// triggers, or under a binder that captures a local of the bound value
/// (`val_locals`) count as `blocked`: the binding can be dropped when there
/// are no uses at all, and inlined only when no use is blocked.
fn count_uses<'vir>(
    name: &str,
    val_locals: &HashSet<&'vir str>,
    e: ExprDyn<'vir>,
    blocked: bool,
    out: &mut Uses,
) {
    macro_rules! go {
        ($e:expr) => {
            count_uses(name, val_locals, $e, blocked, out)
        };
    }
    match e.kind {
        ExprKindGenData::Local(l) => {
            if l.name == name {
                if blocked {
                    out.blocked += 1;
                } else {
                    out.free += 1;
                }
            }
        }
        ExprKindGenData::Const(_)
        | ExprKindGenData::Result(_)
        | ExprKindGenData::Lazy(_)
        | ExprKindGenData::Todo(_) => (),
        ExprKindGenData::Field(recv, _) => go!(recv.as_dyn()),
        ExprKindGenData::Old(o) => count_uses(name, val_locals, o.expr, true, out),
        ExprKindGenData::AccField(a) => {
            go!(a.recv.as_dyn());
            if let Some(p) = a.perm {
                go!(p.as_dyn());
            }
        }
        ExprKindGenData::Unfolding(u) => {
            for arg in u.target.args {
                go!(arg);
            }
            if let Some(p) = u.target.perm {
                go!(p.as_dyn());
            }
            go!(u.expr);
        }
        ExprKindGenData::UnOp(u) => go!(u.expr.as_dyn()),
        ExprKindGenData::BinOp(b) => {
            go!(b.lhs);
            go!(b.rhs);
        }
        ExprKindGenData::CollectionBinOp(b) => {
            go!(b.lhs);
            go!(b.rhs);
        }
        ExprKindGenData::CollectionLiteral(l) => l.values.iter().for_each(|v| go!(v)),
        ExprKindGenData::CollectionUpdate(u) => {
            go!(u.target);
            go!(u.key);
            go!(u.val);
        }
        ExprKindGenData::CollectionLen(inner)
        | ExprKindGenData::MapDomain(inner)
        | ExprKindGenData::MapRange(inner) => go!(inner),
        ExprKindGenData::Ternary(t) => {
            go!(t.cond.as_dyn());
            go!(t.then);
            go!(t.else_);
        }
        ExprKindGenData::Forall(ForallGenData {
            qvars,
            triggers,
            body,
        })
        | ExprKindGenData::Exists(ExistsGenData {
            qvars,
            triggers,
            body,
        }) => {
            if qvars.iter().any(|q| q.name == name) {
                return;
            }
            for t in *triggers {
                for e in t.exprs {
                    count_uses(name, val_locals, e, true, out);
                }
            }
            let captures = qvars.iter().any(|q| val_locals.contains(q.name));
            count_uses(name, val_locals, body.as_dyn(), blocked || captures, out);
        }
        ExprKindGenData::Let(l) => {
            go!(l.val);
            if l.name != name {
                let captures = val_locals.contains(l.name);
                count_uses(name, val_locals, l.expr, blocked || captures, out);
            }
        }
        ExprKindGenData::FuncApp(app) => app.args.iter().for_each(|a| go!(a)),
        ExprKindGenData::PredicateApp(p) => {
            p.args.iter().for_each(|a| go!(a));
            if let Some(perm) = p.perm {
                go!(perm.as_dyn());
            }
        }
        // Wands are never rewritten, so occurrences inside them must keep
        // their binding.
        ExprKindGenData::Wand(w) => {
            count_uses(name, val_locals, w.lhs.as_dyn(), true, out);
            count_uses(name, val_locals, w.rhs.as_dyn(), true, out);
        }
        ExprKindGenData::InhaleExhale(ie) => {
            go!(ie.inhale.as_dyn());
            go!(ie.exhale.as_dyn());
        }
        ExprKindGenData::AdtDestructor(recv, _) | ExprKindGenData::AdtDiscriminator(recv, _) => {
            go!(recv)
        }
    }
}

/// Collects every local name occurring in `e` (a superset of its free
/// locals, which is all the capture check needs).
fn collect_locals<'vir>(e: ExprDyn<'vir>, out: &mut HashSet<&'vir str>) {
    macro_rules! go {
        ($e:expr) => {
            collect_locals($e, out)
        };
    }
    match e.kind {
        ExprKindGenData::Local(l) => {
            out.insert(l.name);
        }
        ExprKindGenData::Const(_)
        | ExprKindGenData::Result(_)
        | ExprKindGenData::Lazy(_)
        | ExprKindGenData::Todo(_) => (),
        ExprKindGenData::Field(recv, _) => go!(recv.as_dyn()),
        ExprKindGenData::Old(o) => go!(o.expr),
        ExprKindGenData::AccField(a) => {
            go!(a.recv.as_dyn());
            if let Some(p) = a.perm {
                go!(p.as_dyn());
            }
        }
        ExprKindGenData::Unfolding(u) => {
            for arg in u.target.args {
                go!(arg);
            }
            if let Some(p) = u.target.perm {
                go!(p.as_dyn());
            }
            go!(u.expr);
        }
        ExprKindGenData::UnOp(u) => go!(u.expr.as_dyn()),
        ExprKindGenData::BinOp(b) => {
            go!(b.lhs);
            go!(b.rhs);
        }
        ExprKindGenData::CollectionBinOp(b) => {
            go!(b.lhs);
            go!(b.rhs);
        }
        ExprKindGenData::CollectionLiteral(l) => l.values.iter().for_each(|v| go!(v)),
        ExprKindGenData::CollectionUpdate(u) => {
            go!(u.target);
            go!(u.key);
            go!(u.val);
        }
        ExprKindGenData::CollectionLen(inner)
        | ExprKindGenData::MapDomain(inner)
        | ExprKindGenData::MapRange(inner) => go!(inner),
        ExprKindGenData::Ternary(t) => {
            go!(t.cond.as_dyn());
            go!(t.then);
            go!(t.else_);
        }
        ExprKindGenData::Forall(ForallGenData { triggers, body, .. })
        | ExprKindGenData::Exists(ExistsGenData { triggers, body, .. }) => {
            for t in *triggers {
                t.exprs.iter().for_each(|e| go!(e));
            }
            go!(body.as_dyn());
        }
        ExprKindGenData::Let(l) => {
            go!(l.val);
            go!(l.expr);
        }
        ExprKindGenData::FuncApp(app) => app.args.iter().for_each(|a| go!(a)),
        ExprKindGenData::PredicateApp(p) => {
            p.args.iter().for_each(|a| go!(a));
            if let Some(perm) = p.perm {
                go!(perm.as_dyn());
            }
        }
        ExprKindGenData::Wand(w) => {
            go!(w.lhs.as_dyn());
            go!(w.rhs.as_dyn());
        }
        ExprKindGenData::InhaleExhale(ie) => {
            go!(ie.inhale.as_dyn());
            go!(ie.exhale.as_dyn());
        }
        ExprKindGenData::AdtDestructor(recv, _) | ExprKindGenData::AdtDiscriminator(recv, _) => {
            go!(recv)
        }
    }
}
