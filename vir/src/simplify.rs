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
//! declarations ([`SimplifyCtx`]), which also ground the injectivity the
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
//! Magic wands are left untouched, wherever they occur: Viper matches
//! packaged wand instances syntactically, and evaluates the heap-dependent
//! subterms of a wand only when applying it, in the order of its conjuncts,
//! so moving them around inside a wand changes which permissions are there.

use std::collections::{HashMap, HashSet};

use prusti_rustc_interface::data_structures::fx::FxHashSet;

use crate::{
    collect_locals, data::*, gendata::*, refs::*, CastType, Foldable, Folder, ViperIdent, VirCtxt,
    Visitable, Visitor,
};

/// What the simplification knows about the program: its adt constructors and
/// destructors, its total functions and the literal inverses its encoder
/// declares, used to recognize the foldable applications.
pub struct SimplifyCtx<'vir> {
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

impl<'vir> SimplifyCtx<'vir> {
    pub fn new(
        adts: &[Adt<'vir>],
        domains: &[Domain<'vir>],
        functions: &[Function<'vir>],
        literal_inverses: &[(ViperIdent<'vir>, ViperIdent<'vir>)],
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
            literal_inverses: literal_inverses
                .iter()
                .map(|(outer, inner)| (outer.to_str(), inner.to_str()))
                .collect(),
        }
    }
}

/// Simplifies the expressions of a program item (a domain, predicate,
/// function or method).
pub fn simplify<'vir, 'tcx, T: Foldable<'vir, (), !> + Copy>(
    vcx: &'vir VirCtxt<'tcx>,
    ctx: &SimplifyCtx<'vir>,
    item: T,
) -> T {
    let mut s = Simplifier::new(vcx, ctx);
    item.fold_with(&mut Roots(&mut s)).unwrap_or(item)
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
    ctx: &'enc SimplifyCtx<'vir>,
    env: HashMap<&'vir str, Binding<'vir>>,
}

/// Hands the roots of the expression trees of an item (contract clauses,
/// invariants, bodies, axioms and statement operands) to
/// [`Simplifier::root`].
struct Roots<'s, 'enc, 'vir, 'tcx>(&'s mut Simplifier<'enc, 'vir, 'tcx>);

impl<'vir> Folder<'vir, (), !> for Roots<'_, '_, 'vir, '_> {
    fn fold_expr(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        self.0.root(e)
    }

    fn fold_wand(&mut self, _: Wand<'vir>) -> Option<Wand<'vir>> {
        None
    }
}

impl<'vir> Folder<'vir, (), !> for Simplifier<'_, 'vir, '_> {
    fn fold_expr(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        self.simplify(e)
    }

    fn fold_wand(&mut self, _: Wand<'vir>) -> Option<Wand<'vir>> {
        None
    }
}

impl<'enc, 'vir, 'tcx> Simplifier<'enc, 'vir, 'tcx> {
    fn new(vcx: &'vir VirCtxt<'tcx>, ctx: &'enc SimplifyCtx<'vir>) -> Self {
        Self {
            vcx,
            ctx,
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

    fn expr(&mut self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.simplify(e).unwrap_or(e)
    }

    /// Simplifies the root of an expression tree (a contract clause,
    /// invariant, body or statement operand), keeping the root's span. Viper
    /// blames e.g. a failing postcondition on the clause's root node, and
    /// the error handler is registered on the span of that node only (see
    /// `realloc_span`); a rule replacing the root by a subexpression would
    /// make the error impossible to backtranslate.
    fn root(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        let simplified = self.simplify(e)?;
        // A root without a span has no handler; keep the result's own.
        if e.span.is_none() {
            return Some(simplified);
        }
        Some(self.vcx.alloc(ExprGenData::new_inner(
            simplified.kind,
            simplified.debug_info,
            e.span,
            simplified.ty(),
        )))
    }

    /// The simplified `e`, `None` if no rule applies to it or any of its
    /// subexpressions.
    fn simplify(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        match e.kind {
            // The bound value is already simplified in its own scope; do not
            // re-process it (its locals refer to outer bindings).
            ExprKindGenData::Local(local) => {
                return self.env.get(local.name).filter(|b| b.subst).map(|b| b.val);
            }
            ExprKindGenData::Old(_) => {
                // Only heap-independent bindings survive into `old(..)`.
                let saved = self.env.clone();
                self.env.retain(|_, b| {
                    matches!(
                        b.val.kind,
                        ExprKindGenData::Local(_) | ExprKindGenData::Const(_)
                    )
                });
                let folded = e.super_fold_with(self);
                self.env = saved;
                return folded;
            }
            ExprKindGenData::Forall(q) => {
                let body = self.quantifier_body(q.qvars, q.body.as_dyn())?;
                if bool_lit(body).is_some() {
                    return Some(self.mk(e, body.kind));
                }
                return Some(
                    self.mk(
                        e,
                        self.vcx
                            .alloc(ExprKindGenData::Forall(self.vcx.alloc(ForallGenData {
                                qvars: q.qvars,
                                triggers: q.triggers,
                                body: body.inner_cast_ty(),
                            }))),
                    ),
                );
            }
            ExprKindGenData::Exists(q) => {
                let body = self.quantifier_body(q.qvars, q.body.as_dyn())?;
                if bool_lit(body).is_some() {
                    return Some(self.mk(e, body.kind));
                }
                return Some(
                    self.mk(
                        e,
                        self.vcx
                            .alloc(ExprKindGenData::Exists(self.vcx.alloc(ExistsGenData {
                                qvars: q.qvars,
                                triggers: q.triggers,
                                body: body.inner_cast_ty(),
                            }))),
                    ),
                );
            }
            ExprKindGenData::Let(l) => return self.let_expr(e, l),
            _ => (),
        }
        let folded = e.super_fold_with(self);
        self.rewrite(folded.unwrap_or(e)).or(folded)
    }

    /// The rules applying to `e`, whose subexpressions are simplified
    /// already. `None` if none applies.
    fn rewrite(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        match e.kind {
            ExprKindGenData::UnOp(u) => match (u.kind, u.expr.kind) {
                (UnOpKind::Not, _) => self.fold_not(e, u.expr.as_dyn()),
                (UnOpKind::Neg, ExprKindGenData::UnOp(i)) if i.kind == UnOpKind::Neg => {
                    Some(i.expr.as_dyn())
                }
                (UnOpKind::PermNeg, ExprKindGenData::UnOp(i)) if i.kind == UnOpKind::PermNeg => {
                    Some(i.expr.as_dyn())
                }
                _ => None,
            },
            ExprKindGenData::BinOp(b) => {
                let adt = match b.kind {
                    BinOpKind::CmpEq => self.fold_eq(e, b.lhs, b.rhs),
                    BinOpKind::CmpNe => self.fold_eq(e, b.lhs, b.rhs).map(|eq| self.mk_not(e, eq)),
                    _ => None,
                };
                adt.or_else(|| self.fold_binop(e, e.ty(), b.kind, b.lhs, b.rhs))
            }
            ExprKindGenData::Ternary(t) => {
                self.fold_ternary(e, e.ty(), t.cond.as_dyn(), t.then, t.else_)
            }
            ExprKindGenData::FuncApp(app) => self
                .fold_eta(app.target, app.args, app.result_ty)
                .or_else(|| {
                    self.fold_literal_inverse(app.target, app.args)
                        .map(|k| self.mk(e, k.kind))
                }),
            ExprKindGenData::AdtDestructor(recv, destr) => self.fold_destructor(e, recv, destr),
            _ => None,
        }
    }

    /// The simplified body of a quantifier over `qvars`, see
    /// [`Self::quantifier_env`].
    fn quantifier_body(
        &mut self,
        qvars: &'vir [crate::LocalDeclDyn<'vir>],
        body: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        let saved = self.quantifier_env(qvars);
        let body = self.simplify(body);
        self.env = saved;
        body
    }

    /// Saves the environment and drops the entries a quantifier invalidates:
    /// shadowed names and bindings whose locals the quantified variables
    /// would capture. This must match the capture rule of [`UseCounter`]: a
    /// binding retained here is substituted in the body, so [`UseCounter`]
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
            let mut locals = FxHashSet::default();
            collect_locals(b.val, &mut locals);
            qvars.iter().all(|q| !locals.contains(q.name))
        });
        saved
    }

    fn let_expr(
        &mut self,
        e: ExprDyn<'vir>,
        l: &'vir LetGenData<'vir, (), !>,
    ) -> Option<ExprDyn<'vir>> {
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
        if let Some(folded) = self.fold_let(l.name, val, body) {
            return Some(folded);
        }
        if std::ptr::eq(val, l.val) && std::ptr::eq(body, l.expr) {
            return None;
        }
        Some(self.let_node(e, l.name, val, body))
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
        self.fold_let(name, val, body)
            .unwrap_or_else(|| self.let_node(orig, name, val, body))
    }

    /// The body of `let name = val in body` when the binding is unused, or
    /// with the binding inlined when used exactly once.
    fn fold_let(
        &mut self,
        name: &'vir str,
        val: ExprDyn<'vir>,
        body: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        let mut uses = UseCounter::new(name, val);
        body.visit_with(&mut uses);
        if uses.free + uses.blocked == 0 {
            return Some(body);
        }
        if uses.blocked == 0 && uses.free == 1 {
            let prev = self.env.insert(name, Binding { val, subst: true });
            let body = self.expr(body);
            self.restore(name, prev);
            return Some(body);
        }
        None
    }

    fn let_node(
        &self,
        orig: ExprDyn<'vir>,
        name: &'vir str,
        val: ExprDyn<'vir>,
        body: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
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

    /// `cond ? then : else_` of type `ty`, with the span of `orig`.
    fn mk_ternary(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        cond: ExprDyn<'vir>,
        then: ExprDyn<'vir>,
        else_: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        self.fold_ternary(orig, ty, cond, then, else_)
            .unwrap_or_else(|| self.ternary_node(orig, ty, cond, then, else_))
    }

    /// The rules for `cond ? then : else_`. When both branches apply the
    /// same adt constructor or total function, the application moves out:
    /// `c ? f(a..) : f(b..)` is `f(c ? a_0 : b_0, ..)`, recursively. A
    /// function with a precondition stays inside: Silicon cannot find a
    /// permission whose receiver is a ternary unless the condition is
    /// decided.
    fn fold_ternary(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        cond: ExprDyn<'vir>,
        then: ExprDyn<'vir>,
        else_: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        if let Some(b) = bool_lit(cond) {
            return Some(if b { then } else { else_ });
        }
        let (orig_then, orig_else) = (then, else_);
        let then = match then.kind {
            ExprKindGenData::Ternary(t) if syntactic_eq(t.cond.as_dyn(), cond) => t.then,
            _ => then,
        };
        let else_ = match else_.kind {
            ExprKindGenData::Ternary(t) if syntactic_eq(t.cond.as_dyn(), cond) => t.else_,
            _ => else_,
        };
        if syntactic_eq(then, else_) {
            return Some(then);
        }
        let bool_ty = crate::TYPE_BOOL.as_dyn();
        // Nested ternaries sharing a branch merge their conditions.
        if let ExprKindGenData::Ternary(t) = then.kind {
            if syntactic_eq(t.then, else_) {
                let not = self.mk_not(orig, t.cond.as_dyn());
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::And, cond, not);
                return Some(self.mk_ternary(orig, ty, cond, t.else_, else_));
            }
            if syntactic_eq(t.else_, else_) {
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::And, cond, t.cond.as_dyn());
                return Some(self.mk_ternary(orig, ty, cond, t.then, else_));
            }
        }
        if let ExprKindGenData::Ternary(t) = else_.kind {
            if syntactic_eq(then, t.then) {
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, t.cond.as_dyn());
                return Some(self.mk_ternary(orig, ty, cond, then, t.else_));
            }
            if syntactic_eq(then, t.else_) {
                let not = self.mk_not(orig, t.cond.as_dyn());
                let cond = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, not);
                return Some(self.mk_ternary(orig, ty, cond, then, t.then));
            }
        }
        if ty == bool_ty {
            match else_.kind {
                ExprKindGenData::BinOp(b)
                    if b.kind == BinOpKind::Implies && syntactic_eq(then, b.rhs) =>
                {
                    let lhs = self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, b.lhs);
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::Implies, lhs, then));
                }
                _ => (),
            }
            match then.kind {
                ExprKindGenData::BinOp(b)
                    if b.kind == BinOpKind::Implies && syntactic_eq(b.rhs, else_) =>
                {
                    let not = self.mk_not(orig, cond);
                    let lhs = self.mk_binop(orig, bool_ty, BinOpKind::Or, not, b.lhs);
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::Implies, lhs, else_));
                }
                _ => (),
            }
            match (bool_lit(then), bool_lit(else_)) {
                (Some(true), Some(false)) => return Some(cond),
                (Some(false), Some(true)) => return Some(self.mk_not(orig, cond)),
                (Some(false), None) => {
                    let not = self.mk_not(orig, cond);
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::And, not, else_));
                }
                (Some(true), None) => {
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::Or, cond, else_))
                }
                (None, Some(false)) => {
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::And, cond, then))
                }
                (None, Some(true)) => {
                    return Some(self.mk_binop(orig, bool_ty, BinOpKind::Implies, cond, then))
                }
                _ => (),
            }
        }
        match (then.kind, else_.kind) {
            (ExprKindGenData::FuncApp(a), ExprKindGenData::FuncApp(b))
                if a.target == b.target
                    && a.args.len() == b.args.len()
                    && a.typ_var_map == b.typ_var_map
                    && a.args.iter().zip(b.args).all(|(x, y)| x.ty() == y.ty())
                    && (self.ctx.constructors.contains_key(a.target)
                        || self.ctx.total_functions.contains(a.target)) =>
            {
                let args = a
                    .args
                    .iter()
                    .zip(b.args)
                    .map(|(x, y)| self.mk_ternary(orig, x.ty(), cond, x, y))
                    .collect::<Vec<_>>();
                let app = ExprKindGenData::FuncApp(self.vcx.alloc(FuncAppGenData {
                    target: a.target,
                    args: self.vcx.alloc_slice(&args),
                    result_ty: a.result_ty,
                    typ_var_map: a.typ_var_map,
                }));
                Some(self.mk_typed(orig, ty, self.vcx.alloc(app)))
            }
            _ => (!std::ptr::eq(then, orig_then) || !std::ptr::eq(else_, orig_else))
                .then(|| self.ternary_node(orig, ty, cond, then, else_)),
        }
    }

    fn ternary_node(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        cond: ExprDyn<'vir>,
        then: ExprDyn<'vir>,
        else_: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        let kind = ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
            cond: cond.inner_cast_ty(),
            then,
            else_,
        }));
        self.mk_typed(orig, ty, self.vcx.alloc(kind))
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
                let (cons, idx) = *self.ctx.destructors.get(destr.name)?;
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
    /// [`SimplifyCtx::eta`].
    fn fold_eta(
        &self,
        target: &'vir str,
        args: &'vir [ExprDyn<'vir>],
        result_ty: TypeDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        if !self.ctx.eta.contains(target) {
            return None;
        }
        let fields = *self.ctx.constructors.get(target)?;
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
    /// [`SimplifyCtx::literal_inverses`] yields `k`.
    fn fold_literal_inverse(
        &self,
        target: &'vir str,
        args: &'vir [ExprDyn<'vir>],
    ) -> Option<ExprDyn<'vir>> {
        let inner = *self.ctx.literal_inverses.get(target)?;
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
            || !self.ctx.constructors.contains_key(la.target)
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

    /// `!e` with the span of `orig`.
    fn mk_not(&self, orig: ExprDyn<'vir>, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.fold_not(orig, e).unwrap_or_else(|| {
            self.mk_typed(
                orig,
                crate::TYPE_BOOL.as_dyn(),
                self.vcx
                    .alloc(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
                        kind: UnOpKind::Not,
                        expr: e.inner_cast_ty(),
                    }))),
            )
        })
    }

    /// The rules for `!e`: literals and double negations fold, and a negated
    /// comparison flips its operator.
    fn fold_not(&self, orig: ExprDyn<'vir>, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        if let Some(b) = bool_lit(e) {
            return Some(self.mk_bool_lit(orig, !b));
        }
        match e.kind {
            ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Not => Some(u.expr.as_dyn()),
            ExprKindGenData::BinOp(b) => {
                let kind = ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                    kind: negated_cmp(b.kind)?,
                    lhs: b.lhs,
                    rhs: b.rhs,
                }));
                Some(self.mk_typed(orig, crate::TYPE_BOOL.as_dyn(), self.vcx.alloc(kind)))
            }
            _ => None,
        }
    }

    /// `lhs <kind> rhs` of type `ty` with the span of `orig`.
    fn mk_binop(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        kind: BinOpKind,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> ExprDyn<'vir> {
        self.fold_binop(orig, ty, kind, lhs, rhs)
            .unwrap_or_else(|| {
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

    /// The rules for `lhs <kind> rhs`: boolean and integer literal operands
    /// and reflexive (in)equalities fold.
    fn fold_binop(
        &self,
        orig: ExprDyn<'vir>,
        ty: TypeDyn<'vir>,
        kind: BinOpKind,
        lhs: ExprDyn<'vir>,
        rhs: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        let (bl, br) = (bool_lit(lhs), bool_lit(rhs));
        let (il, ir) = (int_lit(lhs), int_lit(rhs));
        let lit = |b| Some(self.mk_bool_lit(orig, b));
        let int = |v: Option<i128>| v.map(|v| self.mk_int_lit(orig, ty, v));
        match kind {
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

/// Counts the uses of `name` in an expression. Occurrences inside `old(..)`,
/// inside magic wands or triggers, or under a binder that captures a local
/// of the bound value count as `blocked`: the binding can be dropped when
/// there are no uses at all, and inlined only when no use is blocked.
struct UseCounter<'vir> {
    name: &'vir str,
    val_locals: FxHashSet<&'vir str>,
    in_blocked: bool,
    free: usize,
    blocked: usize,
}

impl<'vir> UseCounter<'vir> {
    fn new(name: &'vir str, val: ExprDyn<'vir>) -> Self {
        let mut val_locals = FxHashSet::default();
        collect_locals(val, &mut val_locals);
        Self {
            name,
            val_locals,
            in_blocked: false,
            free: 0,
            blocked: 0,
        }
    }

    /// Runs `visit` with occurrences counted as blocked if `blocked`.
    fn blocking(&mut self, blocked: bool, visit: impl FnOnce(&mut Self)) {
        let outer = self.in_blocked;
        self.in_blocked |= blocked;
        visit(self);
        self.in_blocked = outer;
    }
}

impl<'vir> Visitor<'vir, (), !> for UseCounter<'vir> {
    fn visit_expr(&mut self, e: ExprDyn<'vir>) {
        match e.kind {
            ExprKindGenData::Local(l) => {
                if l.name == self.name {
                    if self.in_blocked {
                        self.blocked += 1;
                    } else {
                        self.free += 1;
                    }
                }
            }
            ExprKindGenData::Old(_) | ExprKindGenData::Wand(_) => {
                self.blocking(true, |s| e.super_visit_with(s))
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
                if qvars.iter().any(|q| q.name == self.name) {
                    return;
                }
                self.blocking(true, |s| triggers.visit_with(s));
                let captures = qvars.iter().any(|q| self.val_locals.contains(q.name));
                self.blocking(captures, |s| body.visit_with(s));
            }
            ExprKindGenData::Let(l) => {
                l.val.visit_with(self);
                if l.name != self.name {
                    let captures = self.val_locals.contains(l.name);
                    self.blocking(captures, |s| l.expr.visit_with(s));
                }
            }
            _ => e.super_visit_with(self),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{BinOpKind::*, Dyn, TypeData, TypeKind, TYPE_BOOL, TYPE_INT};

    /// Builds expressions over `Bool` and `Int` locals and the adt
    /// `P = P_cons(f0: Int, f1: Int)`.
    struct Builder<'vir, 'tcx> {
        vcx: &'vir VirCtxt<'tcx>,
        p_ty: TypeDyn<'vir>,
    }

    impl<'vir, 'tcx> Builder<'vir, 'tcx> {
        fn node(&self, kind: ExprKindGenData<'vir, (), !>) -> ExprDyn<'vir> {
            self.vcx
                .alloc(ExprGenData::<_, _, Dyn>::new(self.vcx.alloc(kind)))
        }
        fn local(&self, name: &'vir str, ty: TypeDyn<'vir>) -> ExprDyn<'vir> {
            self.vcx.mk_local_ex(self.vcx.mk_local_decl(name, ty))
        }
        fn b(&self, name: &'vir str) -> ExprDyn<'vir> {
            self.local(name, TYPE_BOOL.as_dyn())
        }
        fn i(&self, name: &'vir str) -> ExprDyn<'vir> {
            self.local(name, TYPE_INT.as_dyn())
        }
        fn int(&self, v: u128) -> ExprDyn<'vir> {
            self.vcx.mk_const_expr(ConstData::Int(v)).as_dyn()
        }
        fn tt(&self) -> ExprDyn<'vir> {
            self.vcx.mk_bool::<true>().as_dyn()
        }
        fn not(&self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
            self.node(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
                kind: UnOpKind::Not,
                expr: e.inner_cast_ty(),
            })))
        }
        fn bin(&self, kind: BinOpKind, lhs: ExprDyn<'vir>, rhs: ExprDyn<'vir>) -> ExprDyn<'vir> {
            self.node(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
                kind,
                lhs,
                rhs,
            })))
        }
        fn ite(
            &self,
            cond: ExprDyn<'vir>,
            then: ExprDyn<'vir>,
            else_: ExprDyn<'vir>,
        ) -> ExprDyn<'vir> {
            self.node(ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
                cond: cond.inner_cast_ty(),
                then,
                else_,
            })))
        }
        fn let_(&self, name: &'vir str, val: ExprDyn<'vir>, body: ExprDyn<'vir>) -> ExprDyn<'vir> {
            self.node(ExprKindGenData::Let(self.vcx.alloc(LetGenData {
                name,
                val,
                expr: body,
            })))
        }
        fn forall_int(&self, qvar: &'vir str, body: ExprDyn<'vir>) -> ExprDyn<'vir> {
            let qvars = self
                .vcx
                .alloc_slice(&[self.vcx.mk_local_decl(qvar, TYPE_INT)]);
            self.vcx
                .mk_forall_expr::<(), !, _>(qvars, &[], body.inner_cast_ty())
                .as_dyn()
        }
        fn p(&self, args: &[ExprDyn<'vir>]) -> ExprDyn<'vir> {
            self.vcx
                .mk_func_app("P_cons", self.vcx.alloc_slice(args), self.p_ty, &[])
        }
        fn field(&self, recv: ExprDyn<'vir>, name: &'vir str) -> ExprDyn<'vir> {
            let destr = self.vcx.mk_adt_destructor(name, self.p_ty, TYPE_INT);
            self.vcx.mk_adt_destructor_expr(recv, destr).as_dyn()
        }
    }

    /// Simplifies the expression `build` makes and checks the result's Viper
    /// syntax with `check`.
    fn check_with(
        build: impl for<'vir, 'tcx> FnOnce(&Builder<'vir, 'tcx>) -> ExprDyn<'vir>,
        check: impl FnOnce(&str),
    ) {
        crate::init_vcx(VirCtxt::new_without_tcx());
        crate::with_vcx(|vcx| {
            let fields = vcx.alloc_slice(&[
                vcx.mk_local_decl("f0", TYPE_INT),
                vcx.mk_local_decl("f1", TYPE_INT),
            ]);
            let cons = vcx.mk_adt_constructor::<(), !, _>("P_cons", fields);
            let adt = vcx.mk_adt(crate::ViperIdent::new("P"), &[], vcx.alloc_slice(&[cons]));
            let ctx = SimplifyCtx::new(&[adt], &[], &[], &[]);
            let p_ty = vcx.alloc(TypeData::<Dyn>::new(TypeKind::Domain("P", &[])));
            let e = build(&Builder { vcx, p_ty });
            let mut s = Simplifier::new(vcx, &ctx);
            check(&format!("{:?}", s.expr(e)));
        });
    }

    fn check(
        expected: &str,
        build: impl for<'vir, 'tcx> FnOnce(&Builder<'vir, 'tcx>) -> ExprDyn<'vir>,
    ) {
        check_with(build, |actual| assert_eq!(actual, expected));
    }

    #[test]
    fn boolean_literals() {
        check("b", |c| c.not(c.not(c.b("b"))));
        check("(x) >= (y)", |c| c.not(c.bin(CmpLt, c.i("x"), c.i("y"))));
        check("b", |c| c.bin(And, c.tt(), c.b("b")));
        check("true", |c| c.bin(Or, c.b("b"), c.tt()));
        check("!(b)", |c| c.bin(CmpEq, c.b("b"), c.not(c.tt())));
        check("true", |c| c.bin(CmpEq, c.i("x"), c.i("x")));
    }

    #[test]
    fn integer_literals() {
        check("true", |c| {
            c.bin(CmpEq, c.bin(Add, c.int(1), c.int(2)), c.int(3))
        });
        check("-(3)", |c| c.bin(Sub, c.int(2), c.int(5)));
        check("(7) \\ (0)", |c| c.bin(Div, c.int(7), c.int(0)));
    }

    #[test]
    fn ternaries() {
        check("x", |c| c.ite(c.tt(), c.i("x"), c.i("y")));
        check("x", |c| c.ite(c.b("c"), c.i("x"), c.i("x")));
        check("(c) || (b)", |c| c.ite(c.b("c"), c.tt(), c.b("b")));
        check("(c) ==> (b)", |c| c.ite(c.b("c"), c.b("b"), c.tt()));
    }

    #[test]
    fn lets() {
        check("(x) == (y)", |c| {
            c.let_("a", c.i("x"), c.bin(CmpEq, c.i("a"), c.i("y")))
        });
        check("y", |c| c.let_("a", c.i("x"), c.i("y")));
        // Moving a heap-dependent value into `old` or capturing a local of
        // it under a binder would change its meaning.
        check_with(
            |c| {
                let val = c.bin(Add, c.i("x"), c.int(1));
                let old = c.vcx.mk_old_expr(c.i("a")).as_dyn();
                c.let_("a", val, c.bin(CmpEq, old, c.i("y")))
            },
            |actual| assert!(actual.starts_with("(let a =="), "{actual}"),
        );
        check_with(
            |c| {
                let body = c.bin(CmpEq, c.i("a"), c.i("q"));
                c.let_("a", c.i("q"), c.forall_int("q", body))
            },
            |actual| assert!(actual.starts_with("(let a =="), "{actual}"),
        );
    }

    #[test]
    fn adts() {
        check("x", |c| c.field(c.p(&[c.i("x"), c.i("y")]), "f0"));
        check("((x) == (z)) && ((y) == (w))", |c| {
            c.bin(
                CmpEq,
                c.p(&[c.i("x"), c.i("y")]),
                c.p(&[c.i("z"), c.i("w")]),
            )
        });
        check("q", |c| {
            let q = c.local("q", c.p_ty);
            c.p(&[c.field(q, "f0"), c.field(q, "f1")])
        });
        // `(c ? P_cons(x, y) : r).f0` is `c ? x : r.f0`.
        check_with(
            |c| {
                let recv = c.ite(c.b("c"), c.p(&[c.i("x"), c.i("y")]), c.local("r", c.p_ty));
                c.field(recv, "f0")
            },
            |actual| assert_eq!(actual, "c\n? x\n: r.f0"),
        );
    }

    #[test]
    fn unchanged_expressions_are_not_reallocated() {
        crate::init_vcx(VirCtxt::new_without_tcx());
        crate::with_vcx(|vcx| {
            let ctx = SimplifyCtx::new(&[], &[], &[], &[]);
            let ex = |name| vcx.mk_local_ex::<(), !, _>(vcx.mk_local_decl(name, TYPE_INT));
            let e = vcx.mk_eq_expr(ex("x"), ex("y")).as_dyn();
            assert!(Simplifier::new(vcx, &ctx).simplify(e).is_none());
        });
    }
}
