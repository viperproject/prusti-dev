//! Peephole simplification of hole-free expressions, run over the final
//! program (domain axioms, predicates, functions and methods). Quantifier
//! triggers are left as encoded.
//!
//! The rules undo the wrap/unwrap round-trips produced by composing
//! independently encoded snapshot operations (reference snapshots built and
//! immediately dereferenced, generic casts cancelled out, snapshot
//! constructors compared field by field). All rules are local equivalences:
//!  - an adt field read of the matching constructor application yields the
//!    constructor argument; the read distributes over ternaries of which a
//!    branch folds and moves into the body of `let`s,
//!  - `C(p.f_0, .., p.f_n)` for the constructor `C` of a single-constructor
//!    adt is `p`,
//!  - `c ? f(xs..) : f(ys..)` for an adt constructor or total function `f`
//!    is `f(c ? x_0 : y_0, ..)`,
//!  - `C(xs..) == C(ys..)` for an adt constructor `C` is the conjunction of
//!    the pairwise argument equalities (adt constructors are injective),
//!  - `let x = v in b` is dropped when `x` is unused, and inlined when `v` is
//!    a local/constant or `x` is used exactly once,
//!  - `f(g(k))` for an integer literal `k` is `k` when the encoder declares
//!    `f` a literal inverse of `g`,
//!  - boolean and integer operations on literals fold, as do reflexive
//!    (in)equalities, double negations, negated comparisons, ternaries with
//!    a literal condition, equal branches or a literal branch, and
//!    quantifiers with a literal body.
//!
//! Rules may drop subexpressions together with their well-definedness
//! checks: Prusti checks all side conditions explicitly in impure code.
//!
//! Constructors and destructors are recognized via the program's adt
//! declarations ([`AdtIndex`]), which also ground the injectivity the
//! equality rule relies on. The generic casts are such a pair, with
//! `make_generic_X` a constructor of `s_Param` and `make_concrete_X` the
//! destructor of its value field, so `make_concrete_X(make_generic_X(e))`
//! folds to `e`. The other direction, `make_generic_X(make_concrete_X(p))`,
//! is left standing: it needs to know that `p` really inhabits `X`, and it is
//! the canonical form in which other terms for the same value are built.
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

/// The program's adt constructors and destructors and its total functions,
/// used to recognize the foldable applications.
pub struct AdtIndex<'vir> {
    /// Constructor name to its ordered field (destructor) declarations.
    constructors: HashMap<&'vir str, &'vir [crate::LocalDeclDyn<'vir>]>,
    /// Destructor name to its constructor's name and field index.
    destructors: HashMap<&'vir str, (&'vir str, usize)>,
    /// Constructors `C` for which `C(p.f_0, .., p.f_n)` is `p`: those of
    /// single-constructor adts, for which silver's exclusivity axiom states
    /// exactly this, triggered by the field reads. For the variants of a
    /// multi-constructor adt such as `s_Param` it would need the variant of
    /// `p`, and folding a cast round trip `make_generic_X(p.make_concrete_X)`
    /// loses its canonical form wherever `p`'s type is not known.
    eta: HashSet<&'vir str>,
    /// Names of the total functions: domain functions and functions without
    /// preconditions (which therefore cannot read the heap either).
    total_functions: HashSet<&'vir str>,
    /// Pairs `outer` to `inner` for which the encoder declares that
    /// `outer(inner(k))` is `k` for every integer literal `k` in the program
    /// (such as the value and constructor of a primitive snapshot domain,
    /// whose axiom only holds within the type's bounds).
    literal_inverses: HashMap<&'vir str, &'vir str>,
}

impl<'vir> AdtIndex<'vir> {
    pub fn new(
        adts: &[Adt<'vir>],
        domains: &[Domain<'vir>],
        functions: &[Function<'vir>],
        literal_inverses: &[(&'vir str, &'vir str)],
    ) -> Self {
        let total_functions = domains
            .iter()
            .flat_map(|d| d.functions.iter().map(|f| f.name.to_str()))
            .chain(
                functions
                    .iter()
                    .filter(|f| f.pres.is_empty())
                    .map(|f| f.name),
            )
            .collect();
        let mut constructors = HashMap::new();
        let mut destructors = HashMap::new();
        let mut eta = HashSet::new();
        for adt in adts {
            let eta_adt = adt.constructors.len() == 1;
            for cons in adt.constructors {
                constructors.insert(cons.name, cons.args);
                for (idx, field) in cons.args.iter().enumerate() {
                    destructors.insert(field.name, (cons.name, idx));
                }
                if eta_adt {
                    eta.insert(cons.name);
                }
            }
        }
        Self {
            constructors,
            destructors,
            eta,
            total_functions,
            literal_inverses: literal_inverses.iter().copied().collect(),
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

pub fn domain<'vir, 'tcx>(
    vcx: &'vir VirCtxt<'tcx>,
    adts: &AdtIndex<'vir>,
    d: Domain<'vir>,
) -> Domain<'vir> {
    let mut s = Simplifier::new(vcx, adts);
    let axioms = d
        .axioms
        .iter()
        .map(|a| {
            vcx.alloc(DomainAxiomGenData {
                name: a.name,
                expr: s.root(a.expr),
            }) as DomainAxiom<'vir>
        })
        .collect::<Vec<_>>();
    vcx.alloc(DomainGenData {
        name: d.name,
        typarams: d.typarams,
        axioms: vcx.alloc_slice(&axioms),
        functions: d.functions,
        interpretation: d.interpretation,
    })
}

pub fn predicate<'vir, 'tcx>(
    vcx: &'vir VirCtxt<'tcx>,
    adts: &AdtIndex<'vir>,
    p: Predicate<'vir>,
) -> Predicate<'vir> {
    let mut s = Simplifier::new(vcx, adts);
    vcx.alloc(PredicateGenData {
        name: p.name,
        args: p.args,
        expr: s.opt_root(p.expr),
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
                match (u.kind, inner.kind) {
                    (UnOpKind::Not, _) => return self.mk_not(e, inner),
                    (UnOpKind::Neg, ExprKindGenData::UnOp(i)) if i.kind == UnOpKind::Neg => {
                        return i.expr.as_dyn()
                    }
                    (UnOpKind::PermNeg, ExprKindGenData::UnOp(i))
                        if i.kind == UnOpKind::PermNeg =>
                    {
                        return i.expr.as_dyn()
                    }
                    _ => (),
                }
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
                            return self.mk_not(e, eq);
                        }
                    }
                    _ => (),
                }
                self.mk_binop(e, e.ty(), b.kind, lhs, rhs)
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
                if let Some(b) = bool_lit(cond) {
                    return self.expr(if b { t.then } else { t.else_ });
                }
                let then = self.expr(t.then);
                let else_ = self.expr(t.else_);
                self.mk_ternary(e, e.ty(), cond, then, else_)
            }
            ExprKindGenData::Forall(q) => {
                let saved = self.quantifier_env(q.qvars);
                let body = self.expr(q.body.as_dyn());
                self.env = saved;
                if bool_lit(body).is_some() {
                    return self.mk(e, body.kind);
                }
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
                if bool_lit(body).is_some() {
                    return self.mk(e, body.kind);
                }
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
                if let Some(p) = self.fold_eta(app.target, args, app.result_ty) {
                    return p;
                }
                if let Some(k) = self.fold_literal_inverse(app.target, args) {
                    return self.mk(e, k.kind);
                }
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
                if let Some(arg) = self.fold_destructor(e, recv, destr) {
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
        self.mk_let(e, l.name, val, body)
    }

    /// `let name = val in body` for a simplified `val` and `body`, dropping
    /// the binding when unused and inlining it when used exactly once. `orig`
    /// gives the span and type.
    fn mk_let(
        &mut self,
        orig: ExprDyn<'vir>,
        name: &'vir str,
        val: ExprDyn<'vir>,
        body: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        let mut val_locals = HashSet::new();
        collect_locals(val, &mut val_locals);
        let mut uses = Uses::default();
        count_uses(name, &val_locals, body, false, &mut uses);
        if uses.free + uses.blocked == 0 {
            return body;
        }
        if uses.blocked == 0 && uses.free == 1 {
            let prev = self.env.insert(name, Binding { val, subst: true });
            let body = self.expr(body);
            self.restore(name, prev);
            return body;
        }
        self.mk(
            orig,
            self.vcx
                .alloc(ExprKindGenData::Let(self.vcx.alloc(LetGenData {
                    name,
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

    /// `cond ? then : else_` of type `ty`, with the span of `orig`. When both
    /// branches apply the same adt constructor or total function, the
    /// application moves out: `c ? f(a..) : f(b..)` is
    /// `f(c ? a_0 : b_0, ..)`, recursively. A function with a precondition
    /// stays inside: Silicon cannot find a permission whose receiver is a
    /// ternary unless the condition is decided.
    fn mk_ternary(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        cond: ExprDyn<'vir>,
        then: ExprDyn<'vir>,
        else_: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        if let Some(b) = bool_lit(cond) {
            return if b { then } else { else_ };
        }
        let then = match then.kind {
            ExprKindGenData::Ternary(t) if syntactic_eq(t.cond.as_dyn(), cond) => t.then,
            _ => then,
        };
        let else_ = match else_.kind {
            ExprKindGenData::Ternary(t) if syntactic_eq(t.cond.as_dyn(), cond) => t.else_,
            _ => else_,
        };
        if syntactic_eq(then, else_) {
            return then;
        }
        let bool_ty = crate::TYPE_BOOL.as_dyn();
        // Nested ternaries sharing a branch merge their conditions.
        if let ExprKindGenData::Ternary(t) = then.kind {
            if syntactic_eq(t.then, else_) {
                let not = self.mk_not(orig, t.cond.as_dyn());
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::And, cond, not);
                return self.mk_ternary(orig, ty, cond, t.else_, else_);
            }
            if syntactic_eq(t.else_, else_) {
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::And, cond, t.cond.as_dyn());
                return self.mk_ternary(orig, ty, cond, t.then, else_);
            }
        }
        if let ExprKindGenData::Ternary(t) = else_.kind {
            if syntactic_eq(then, t.then) {
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, t.cond.as_dyn());
                return self.mk_ternary(orig, ty, cond, then, t.else_);
            }
            if syntactic_eq(then, t.else_) {
                let not = self.mk_not(orig, t.cond.as_dyn());
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, not);
                return self.mk_ternary(orig, ty, cond, then, t.then);
            }
        }
        if ty == bool_ty {
            match else_.kind {
                ExprKindGenData::BinOp(b)
                    if b.kind == BinOpKind::Implies && syntactic_eq(then, b.rhs) =>
                {
                    let lhs = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, b.lhs);
                    return self.mk_binop(orig, bool_ty, BinOpKind::Implies, lhs, then);
                }
                _ => (),
            }
            match then.kind {
                ExprKindGenData::BinOp(b)
                    if b.kind == BinOpKind::Implies && syntactic_eq(b.rhs, else_) =>
                {
                    let not = self.mk_not(orig, cond);
                    let lhs = self.mk_binop(orig, bool_ty, BinOpKind::Or, not, b.lhs);
                    return self.mk_binop(orig, bool_ty, BinOpKind::Implies, lhs, else_);
                }
                _ => (),
            }
            match (bool_lit(then), bool_lit(else_)) {
                (Some(true), Some(false)) => return cond,
                (Some(false), Some(true)) => return self.mk_not(orig, cond),
                (Some(false), None) => {
                    let not = self.mk_not(orig, cond);
                    return self.mk_binop(orig, bool_ty, BinOpKind::And, not, else_);
                }
                (Some(true), None) => {
                    return self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, else_)
                }
                (None, Some(false)) => {
                    return self.mk_binop(orig, bool_ty, BinOpKind::And, cond, then)
                }
                (None, Some(true)) => {
                    return self.mk_binop(orig, bool_ty, BinOpKind::Implies, cond, then)
                }
                _ => (),
            }
        }
        let kind = match (then.kind, else_.kind) {
            (ExprKindGenData::FuncApp(a), ExprKindGenData::FuncApp(b))
                if a.target == b.target
                    && a.args.len() == b.args.len()
                    && a.typ_var_map == b.typ_var_map
                    && a.args.iter().zip(b.args).all(|(x, y)| x.ty() == y.ty())
                    && (self.adts.constructors.contains_key(a.target)
                        || self.adts.total_functions.contains(a.target)) =>
            {
                let args = a
                    .args
                    .iter()
                    .zip(b.args)
                    .map(|(x, y)| self.mk_ternary(orig, x.ty(), cond, x, y))
                    .collect::<Vec<_>>();
                ExprKindGenData::FuncApp(self.vcx.alloc(FuncAppGenData {
                    target: a.target,
                    args: self.vcx.alloc_slice(&args),
                    result_ty: a.result_ty,
                    typ_var_map: a.typ_var_map,
                }))
            }
            _ => ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
                cond: cond.inner_cast_ty(),
                then,
                else_,
            })),
        };
        self.vcx.alloc(ExprGenData::new_inner(
            self.vcx.alloc(kind),
            orig.debug_info,
            orig.span,
            ty,
        ))
    }

    /// An adt field read of the matching constructor application yields the
    /// constructor argument. The read distributes over a ternary receiver
    /// (`(c ? a : b).f` is `c ? a.f : b.f`) when at least one branch folds,
    /// so the read is never duplicated, and moves into the body of a `let`
    /// receiver. `orig` is the field read, whose span and type such a
    /// ternary or `let` takes.
    fn fold_destructor(
        &mut self,
        orig: ExprDyn<'vir>,
        recv: ExprDyn<'vir>,
        destr: AdtDestructor<'vir, crate::Dyn, crate::Dyn>,
    ) -> Option<ExprDyn<'vir>> {
        let recv = self.resolve(recv);
        match recv.kind {
            ExprKindGenData::Let(l) => {
                let prev = self.env.insert(
                    l.name,
                    Binding {
                        val: l.val,
                        subst: false,
                    },
                );
                let body = self.fold_destructor(orig, l.expr, destr);
                self.restore(l.name, prev);
                Some(self.mk_let(orig, l.name, l.val, body?))
            }
            ExprKindGenData::Ternary(t) => {
                let then = self.fold_destructor(orig, t.then, destr);
                let else_ = self.fold_destructor(orig, t.else_, destr);
                if then.is_none() && else_.is_none() {
                    return None;
                }
                let read = |branch| {
                    self.mk(
                        orig,
                        self.vcx
                            .alloc(ExprKindGenData::AdtDestructor(branch, destr)),
                    )
                };
                let then = then.unwrap_or_else(|| read(t.then));
                let else_ = else_.unwrap_or_else(|| read(t.else_));
                Some(self.mk_ternary(orig, orig.ty(), t.cond.as_dyn(), then, else_))
            }
            ExprKindGenData::FuncApp(app) => {
                let (cons, idx) = *self.adts.destructors.get(destr.name)?;
                if app.target != cons {
                    return None;
                }
                let arg = *app.args.get(idx)?;
                (recv.ty() == destr.input && arg.ty() == destr.ty).then_some(arg)
            }
            _ => None,
        }
    }

    /// A constructor application to the fields of one value of that variant,
    /// `C(p.f_0, .., p.f_n)`, yields `p`, for the constructors in
    /// [`AdtIndex::eta`].
    fn fold_eta(
        &self,
        target: &'vir str,
        args: &'vir [ExprDyn<'vir>],
        result_ty: TypeDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        if !self.adts.eta.contains(target) {
            return None;
        }
        let fields = *self.adts.constructors.get(target)?;
        if fields.len() != args.len() {
            return None;
        }
        let mut recv = None;
        for (arg, field) in args.iter().zip(fields) {
            let ExprKindGenData::AdtDestructor(p, destr) = arg.kind else {
                return None;
            };
            if destr.name != field.name || !recv.is_none_or(|r| syntactic_eq(r, p)) {
                return None;
            }
            recv = Some(*p);
        }
        recv.filter(|p| p.ty() == result_ty)
    }

    /// `outer(inner(k))` for an integer literal `k` and a pair in
    /// [`AdtIndex::literal_inverses`] yields `k`.
    fn fold_literal_inverse(
        &self,
        target: &'vir str,
        args: &'vir [ExprDyn<'vir>],
    ) -> Option<ExprDyn<'vir>> {
        let inner = *self.adts.literal_inverses.get(target)?;
        let [arg] = args else {
            return None;
        };
        let ExprKindGenData::FuncApp(app) = self.resolve(arg).kind else {
            return None;
        };
        let [k] = app.args else {
            return None;
        };
        let lit = match k.kind {
            ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Neg => u.expr.as_dyn(),
            _ => *k,
        };
        (app.target == inner && matches!(lit.kind, ExprKindGenData::Const(ConstData::Int(_))))
            .then_some(*k)
    }

    /// Simplified equality of two snapshots, if a rule applies: applications
    /// of the same adt constructor compare pairwise (adt constructors are
    /// injective).
    fn fold_eq(
        &mut self,
        orig: ExprDyn<'vir>,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
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
        self.mk_binop(orig, crate::TYPE_BOOL.as_dyn(), BinOpKind::CmpEq, lhs, rhs)
    }

    fn mk_and(&mut self, exprs: Vec<ExprDyn<'vir>>) -> ExprDyn<'vir> {
        let mut conjuncts = exprs.into_iter();
        let Some(first) = conjuncts.next() else {
            return self.vcx.mk_bool::<true>().as_dyn();
        };
        conjuncts.fold(first, |acc, e| {
            self.mk_binop(acc, crate::TYPE_BOOL.as_dyn(), BinOpKind::And, acc, e)
        })
    }

    /// `kind` with the span of `orig` and type `ty`.
    fn mk_typed(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        kind: ExprKind<'vir>,
    ) -> ExprDyn<'vir> {
        self.vcx
            .alloc(ExprGenData::new_inner(kind, orig.debug_info, orig.span, ty))
    }

    fn mk_bool_lit(&self, orig: ExprDyn<'vir>, b: bool) -> ExprDyn<'vir> {
        self.mk_typed(
            orig,
            crate::TYPE_BOOL.as_dyn(),
            self.vcx
                .alloc(ExprKindGenData::Const(self.vcx.alloc(ConstData::Bool(b)))),
        )
    }

    /// The integer literal `v` of type `ty`, a negative one as the negation
    /// of its absolute value (as the encoder writes them).
    fn mk_int_lit(&self, orig: ExprDyn<'vir>, ty: TypeDyn<'vir>, v: i128) -> ExprDyn<'vir> {
        let abs = self.mk_typed(
            orig,
            ty,
            self.vcx.alloc(ExprKindGenData::Const(
                self.vcx.alloc(ConstData::Int(v.unsigned_abs())),
            )),
        );
        if v >= 0 {
            return abs;
        }
        self.mk_typed(
            orig,
            ty,
            self.vcx
                .alloc(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
                    kind: UnOpKind::Neg,
                    expr: abs.inner_cast_ty(),
                }))),
        )
    }

    /// `!e` with the span of `orig`: literals and double negations fold, and
    /// a negated comparison flips its operator.
    fn mk_not(&self, orig: ExprDyn<'vir>, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        if let Some(b) = bool_lit(e) {
            return self.mk_bool_lit(orig, !b);
        }
        let bool_ty = crate::TYPE_BOOL.as_dyn();
        let kind = match e.kind {
            ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Not => return u.expr.as_dyn(),
            ExprKindGenData::BinOp(b) if negated_cmp(b.kind).is_some() => {
                ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                    kind: negated_cmp(b.kind).unwrap(),
                    lhs: b.lhs,
                    rhs: b.rhs,
                }))
            }
            _ => ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
                kind: UnOpKind::Not,
                expr: e.inner_cast_ty(),
            })),
        };
        self.mk_typed(orig, bool_ty, self.vcx.alloc(kind))
    }

    /// `lhs <kind> rhs` of type `ty` with the span of `orig`, folding boolean
    /// and integer literal operands and reflexive (in)equalities.
    fn mk_binop(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        kind: BinOpKind,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        let (bl, br) = (bool_lit(lhs), bool_lit(rhs));
        let (il, ir) = (int_lit(lhs), int_lit(rhs));
        let lit = |b| Some(self.mk_bool_lit(orig, b));
        let int = |v: Option<i128>| v.map(|v| self.mk_int_lit(orig, ty, v));
        let folded = match kind {
            BinOpKind::And => match (bl, br) {
                (Some(true), _) => Some(rhs),
                (_, Some(true)) => Some(lhs),
                (Some(false), _) | (_, Some(false)) => lit(false),
                _ => None,
            },
            BinOpKind::Or => match (bl, br) {
                (Some(false), _) => Some(rhs),
                (_, Some(false)) => Some(lhs),
                (Some(true), _) | (_, Some(true)) => lit(true),
                _ => None,
            },
            BinOpKind::Implies => match (bl, br) {
                (Some(false), _) | (_, Some(true)) => lit(true),
                (Some(true), _) => Some(rhs),
                _ => None,
            },
            BinOpKind::CmpEq | BinOpKind::CmpNe => {
                let eq = kind == BinOpKind::CmpEq;
                match (bl, br) {
                    _ if syntactic_eq(lhs, rhs) => lit(eq),
                    (Some(a), Some(b)) => lit((a == b) == eq),
                    (Some(a), None) if a == eq => Some(rhs),
                    (Some(_), None) => Some(self.mk_not(orig, rhs)),
                    (None, Some(b)) if b == eq => Some(lhs),
                    (None, Some(_)) => Some(self.mk_not(orig, lhs)),
                    (None, None) => il.zip(ir).and_then(|(a, b)| lit((a == b) == eq)),
                }
            }
            BinOpKind::CmpGt | BinOpKind::CmpGe | BinOpKind::CmpLt | BinOpKind::CmpLe => {
                il.zip(ir).and_then(|(a, b)| {
                    lit(match kind {
                        BinOpKind::CmpGt => a > b,
                        BinOpKind::CmpGe => a >= b,
                        BinOpKind::CmpLt => a < b,
                        _ => a <= b,
                    })
                })
            }
            BinOpKind::Add => int(il.zip(ir).and_then(|(a, b)| a.checked_add(b))),
            BinOpKind::Sub => int(il.zip(ir).and_then(|(a, b)| a.checked_sub(b))),
            BinOpKind::Mul => int(il.zip(ir).and_then(|(a, b)| a.checked_mul(b))),
            // SMT division and modulo agree with Rust's only for non-negative
            // operands.
            BinOpKind::Div | BinOpKind::Mod => int(il.zip(ir).and_then(|(a, b)| {
                (a >= 0 && b > 0).then(|| if kind == BinOpKind::Div { a / b } else { a % b })
            })),
            _ => None,
        };
        folded.unwrap_or_else(|| {
            self.mk_typed(
                orig,
                ty,
                self.vcx
                    .alloc(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                        kind,
                        lhs,
                        rhs,
                    }))),
            )
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

fn bool_lit(e: ExprDyn<'_>) -> Option<bool> {
    match e.kind {
        ExprKindGenData::Const(ConstData::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// An integer literal, a negative one written as the negation of its
/// absolute value.
fn int_lit(e: ExprDyn<'_>) -> Option<i128> {
    match e.kind {
        ExprKindGenData::Const(ConstData::Int(v)) => i128::try_from(*v).ok(),
        ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Neg => match u.expr.kind {
            ExprKindGenData::Const(ConstData::Int(v)) => i128::try_from(*v).ok().map(|v| -v),
            _ => None,
        },
        _ => None,
    }
}

/// The comparison that is the negation of `kind`, if `kind` is one.
fn negated_cmp(kind: BinOpKind) -> Option<BinOpKind> {
    Some(match kind {
        BinOpKind::CmpEq => BinOpKind::CmpNe,
        BinOpKind::CmpNe => BinOpKind::CmpEq,
        BinOpKind::CmpGt => BinOpKind::CmpLe,
        BinOpKind::CmpLe => BinOpKind::CmpGt,
        BinOpKind::CmpGe => BinOpKind::CmpLt,
        BinOpKind::CmpLt => BinOpKind::CmpGe,
        _ => return None,
    })
}

/// Syntactic equality, conservative (`false` for unhandled kinds).
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
        (ExprKindGenData::UnOp(x), ExprKindGenData::UnOp(y)) => {
            x.kind == y.kind && syntactic_eq(x.expr.as_dyn(), y.expr.as_dyn())
        }
        (ExprKindGenData::BinOp(x), ExprKindGenData::BinOp(y)) => {
            x.kind == y.kind && syntactic_eq(x.lhs, y.lhs) && syntactic_eq(x.rhs, y.rhs)
        }
        (ExprKindGenData::CollectionBinOp(x), ExprKindGenData::CollectionBinOp(y)) => {
            x.kind == y.kind && syntactic_eq(x.lhs, y.lhs) && syntactic_eq(x.rhs, y.rhs)
        }
        (ExprKindGenData::CollectionLiteral(x), ExprKindGenData::CollectionLiteral(y)) => {
            x.ty == y.ty
                && x.values.len() == y.values.len()
                && x.values
                    .iter()
                    .zip(y.values)
                    .all(|(a, b)| syntactic_eq(a, b))
        }
        (ExprKindGenData::CollectionUpdate(x), ExprKindGenData::CollectionUpdate(y)) => {
            syntactic_eq(x.target, y.target)
                && syntactic_eq(x.key, y.key)
                && syntactic_eq(x.val, y.val)
        }
        (ExprKindGenData::CollectionLen(x), ExprKindGenData::CollectionLen(y))
        | (ExprKindGenData::MapDomain(x), ExprKindGenData::MapDomain(y))
        | (ExprKindGenData::MapRange(x), ExprKindGenData::MapRange(y)) => syntactic_eq(x, y),
        (ExprKindGenData::Field(r1, f1), ExprKindGenData::Field(r2, f2)) => {
            f1.name == f2.name && syntactic_eq(r1.as_dyn(), r2.as_dyn())
        }
        (ExprKindGenData::Old(x), ExprKindGenData::Old(y)) => {
            x.label == y.label && syntactic_eq(x.expr, y.expr)
        }
        (ExprKindGenData::Ternary(x), ExprKindGenData::Ternary(y)) => {
            syntactic_eq(x.cond.as_dyn(), y.cond.as_dyn())
                && syntactic_eq(x.then, y.then)
                && syntactic_eq(x.else_, y.else_)
        }
        (ExprKindGenData::AdtDiscriminator(e1, n1), ExprKindGenData::AdtDiscriminator(e2, n2)) => {
            n1 == n2 && syntactic_eq(e1, e2)
        }
        (ExprKindGenData::Result(_), ExprKindGenData::Result(_)) => a.ty() == b.ty(),
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
