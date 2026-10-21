//! The equations, one function per kind of node they rewrite. Each gets the
//! node's simplified operands and returns an equal expression, or `None` if
//! no equation applies. Results are put together with the constructors at
//! the end, which apply the equations to what they build in turn, so a
//! result is simplified as a whole. Every equation makes the expression
//! smaller or moves an operation towards the leaves, so this terminates.

use super::walk::{occurrences, Binding, Simplifier};
use crate::{data::*, gendata::*, refs::*, CastType};

impl<'vir> Simplifier<'_, 'vir, '_> {
    /// Applies the equations of `e`'s kind to `e`, whose subexpressions are
    /// simplified.
    pub(super) fn fold(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        match e.kind {
            ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Not => self.fold_not(u.expr.as_dyn()),
            ExprKindGenData::BinOp(b) => self.fold_bin_op(b.kind, b.lhs, b.rhs),
            ExprKindGenData::Ternary(t) => self.fold_ternary(t.cond.as_dyn(), t.then, t.else_),
            ExprKindGenData::AdtDestructor(recv, destr) => self.fold_field(recv, destr),
            ExprKindGenData::FuncApp(app) => self.fold_app(app),
            ExprKindGenData::Forall(q) => self.fold_quantifier(q.body.as_dyn()),
            ExprKindGenData::Exists(q) => self.fold_quantifier(q.body.as_dyn()),
            ExprKindGenData::Let(l) => self.fold_let(l),
            _ => None,
        }
    }

    /// `let x = v in b`:
    ///  - `let x = v in x` is `v`,
    ///  - `let x = v in b` is `b` when `b` does not mention `x`. The
    ///    traversal has replaced the uses of `x` it could by `v`.
    fn fold_let(&mut self, l: &LetGenData<'vir, (), !>) -> Option<ExprDyn<'vir>> {
        match l.expr.kind {
            ExprKindGenData::Local(x) if x.name == l.name => Some(l.val),
            _ => (occurrences(l.name, l.expr) == 0).then_some(l.expr),
        }
    }

    /// `!e`:
    ///  - `!b` for a literal `b` is the negated literal,
    ///  - `!!a` is `a`,
    ///  - `!(a < b)` is `a >= b`, and likewise for the other comparisons.
    fn fold_not(&mut self, e: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        if let Some(b) = as_bool(e) {
            return Some(self.bool(!b));
        }
        match e.kind {
            ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Not => Some(u.expr.as_dyn()),
            ExprKindGenData::BinOp(b) => {
                let negated = match b.kind {
                    BinOpKind::CmpEq => BinOpKind::CmpNe,
                    BinOpKind::CmpNe => BinOpKind::CmpEq,
                    BinOpKind::CmpGt => BinOpKind::CmpLe,
                    BinOpKind::CmpLe => BinOpKind::CmpGt,
                    BinOpKind::CmpGe => BinOpKind::CmpLt,
                    BinOpKind::CmpLt => BinOpKind::CmpGe,
                    _ => return None,
                };
                Some(self.bin_op(negated, b.lhs, b.rhs))
            }
            _ => None,
        }
    }

    /// `l && r`, `l || r`, `l ==> r`, `l == r` and `l != r`:
    ///  - `true && r` is `r` and `false && r` is `false`, `false || r` is `r`
    ///    and `true || r` is `true`, and likewise with the literal on the
    ///    right,
    ///  - `true ==> r` is `r`, `false ==> r` and `l ==> true` are `true`,
    ///  - `l == true` and `l != false` are `l`, `l == false` and `l != true`
    ///    are `!l`, and likewise with the literal on the left,
    ///  - `C(a_0, ..) == C(b_0, ..)` is `a_0 == b_0 && ..` since adt
    ///    constructors are injective, and `!=` is its negation; the
    ///    applications may be locals bound to them.
    fn fold_bin_op(
        &mut self,
        kind: BinOpKind,
        l: ExprDyn<'vir>,
        r: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        use BinOpKind::*;
        match (kind, as_bool(l), as_bool(r)) {
            (And, Some(true), _) | (Or, Some(false), _) | (Implies, Some(true), _) => Some(r),
            (And, _, Some(true)) | (Or, _, Some(false)) => Some(l),
            (And, Some(false), _) | (And, _, Some(false)) => Some(self.bool(false)),
            (Or, Some(true), _) | (Or, _, Some(true)) => Some(self.bool(true)),
            (Implies, Some(false), _) | (Implies, _, Some(true)) => Some(self.bool(true)),
            (CmpEq | CmpNe, Some(a), Some(b)) => Some(self.bool((a == b) == (kind == CmpEq))),
            (CmpEq | CmpNe, Some(lit), None) => Some(self.eq_literal(kind, lit, r)),
            (CmpEq | CmpNe, None, Some(lit)) => Some(self.eq_literal(kind, lit, l)),
            (CmpEq | CmpNe, None, None) => self.constructor_eq(kind, l, r),
            _ => None,
        }
    }

    /// `e == lit` (or `e != lit`, by `kind`) for a boolean literal `lit`.
    fn eq_literal(&mut self, kind: BinOpKind, lit: bool, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        if lit == (kind == BinOpKind::CmpEq) {
            e
        } else {
            self.not(e)
        }
    }

    fn constructor_eq(
        &mut self,
        kind: BinOpKind,
        l: ExprDyn<'vir>,
        r: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        let (ExprKindGenData::FuncApp(x), ExprKindGenData::FuncApp(y)) =
            (self.resolve(l).kind, self.resolve(r).kind)
        else {
            return None;
        };
        if !self.ctx.constructors.contains_key(x.target) || !same_arg_types(x, y) {
            return None;
        }
        let mut conj = self.bool(true);
        for (a, b) in x.args.iter().zip(y.args) {
            let eq = self.bin_op(BinOpKind::CmpEq, a, b);
            conj = self.bin_op(BinOpKind::And, conj, eq);
        }
        Some(if kind == BinOpKind::CmpEq {
            conj
        } else {
            self.not(conj)
        })
    }

    /// `c ? a : b`:
    ///  - `c ? a : a` is `a`,
    ///  - for booleans, a literal branch turns it into a connective:
    ///    `c ? true : b` is `c || b` (for a pure `b`: Viper rejects e.g.
    ///    `c || acc(x.f)`), `c ? false : b` is `!c && b`, `c ? a : true` is
    ///    `c ==> a` and `c ? a : false` is `c && a`,
    ///  - `c ? f(a_0, ..) : f(b_0, ..)` is `f(c ? a_0 : b_0, ..)` when `f` is
    ///    an adt constructor or a function without a precondition. A function
    ///    with a precondition stays inside: Silicon cannot find a permission
    ///    whose receiver is a ternary unless the condition is decided.
    fn fold_ternary(
        &mut self,
        c: ExprDyn<'vir>,
        a: ExprDyn<'vir>,
        b: ExprDyn<'vir>,
    ) -> Option<ExprDyn<'vir>> {
        if syntactic_eq(a, b) {
            return Some(a);
        }
        match (as_bool(a), as_bool(b)) {
            (Some(true), _) if !self.is_impure(b) => {
                return Some(self.bin_op(BinOpKind::Or, c, b));
            }
            (Some(false), _) => {
                let not_c = self.not(c);
                return Some(self.bin_op(BinOpKind::And, not_c, b));
            }
            (_, Some(true)) => return Some(self.bin_op(BinOpKind::Implies, c, a)),
            (_, Some(false)) => return Some(self.bin_op(BinOpKind::And, c, a)),
            _ => {}
        }
        let (ExprKindGenData::FuncApp(x), ExprKindGenData::FuncApp(y)) = (a.kind, b.kind) else {
            return None;
        };
        let hoistable = same_arg_types(x, y)
            && (self.ctx.constructors.contains_key(x.target)
                || self.ctx.total_functions.contains(x.target));
        if !hoistable {
            return None;
        }
        let args = x
            .args
            .iter()
            .zip(y.args)
            .map(|(p, q)| self.ternary(c, p, q))
            .collect::<Vec<_>>();
        Some(self.app(x, &args))
    }

    /// `r.f` for an adt field `f`:
    ///  - `C(a_0, .., a_n).f_i` is `a_i` for the constructor `C` with fields
    ///    `f_0, .., f_n`, also when `r` is a local bound to such an
    ///    application,
    ///  - `(c ? a : b).f` is `c ? a.f : b.f` when the read folds in a branch,
    ///    so that it is never just duplicated,
    ///  - `(let x = v in b).f` is `let x = v in b.f` when the read folds in
    ///    `b`.
    fn fold_field(
        &mut self,
        r: ExprDyn<'vir>,
        f: AdtDestructor<'vir, crate::Dyn, crate::Dyn>,
    ) -> Option<ExprDyn<'vir>> {
        let resolved = self.resolve(r);
        match resolved.kind {
            ExprKindGenData::FuncApp(app) => {
                let &(cons, idx) = self.ctx.destructors.get(f.name)?;
                let arg = *app.args.get(idx)?;
                (app.target == cons && resolved.ty() == f.input && arg.ty() == f.ty).then_some(arg)
            }
            ExprKindGenData::Ternary(t) => {
                let a = self.fold_field(t.then, f);
                let b = self.fold_field(t.else_, f);
                if a.is_none() && b.is_none() {
                    return None;
                }
                let a = a.unwrap_or_else(|| self.node(ExprKindGenData::AdtDestructor(t.then, f)));
                let b = b.unwrap_or_else(|| self.node(ExprKindGenData::AdtDestructor(t.else_, f)));
                Some(self.ternary(t.cond.as_dyn(), a, b))
            }
            ExprKindGenData::Let(l) => {
                let binding = Binding::new(self.vcx, l.val, l.name, l.expr);
                let expr = self.with_binding(l.name, binding, |s| s.fold_field(l.expr, f))?;
                let (name, val) = (l.name, l.val);
                // The traversal inlines a local the read leaves with one use.
                let moved = self.node(ExprKindGenData::Let(self.vcx.alloc(LetGenData {
                    name,
                    val,
                    expr,
                })));
                Some(self.simplify(moved).unwrap_or(moved))
            }
            _ => None,
        }
    }

    /// `f(a_0, ..)`:
    ///  - `C(p.f_0, .., p.f_n)` is `p` for the constructor `C` of a
    ///    single-constructor adt, whose exclusivity axiom (from silver) states
    ///    exactly this. For the variants of a multi-constructor adt such as
    ///    `s_Param` it would need the variant of `p`.
    ///  - `outer(inner(k))` is `k` for an integer literal `k` in one of the
    ///    ranges of a [`LiteralInverse`](super::LiteralInverse) the encoder
    ///    declares, e.g. `value(cons(5))` of a primitive snapshot domain.
    fn fold_app(&mut self, app: &'vir FuncAppGenData<'vir, (), !>) -> Option<ExprDyn<'vir>> {
        if self.ctx.eta.contains(app.target) {
            let fields = *self.ctx.constructors.get(app.target)?;
            if fields.len() != app.args.len() {
                return None;
            }
            let mut recv = None;
            for (arg, field) in app.args.iter().zip(fields) {
                let ExprKindGenData::AdtDestructor(p, destr) = arg.kind else {
                    return None;
                };
                if destr.name != field.name || !recv.is_none_or(|r| syntactic_eq(r, p)) {
                    return None;
                }
                recv = Some(p);
            }
            return recv.filter(|p| p.ty() == app.result_ty);
        }
        let inverse = self.ctx.literal_inverses.get(app.target)?;
        let [arg] = app.args else {
            return None;
        };
        let ExprKindGenData::FuncApp(inner) = self.resolve(arg).kind else {
            return None;
        };
        let [k] = inner.args else {
            return None;
        };
        let v = as_int(k)?;
        let in_range = |&(min, max): &(ExprInt<'vir>, ExprInt<'vir>)| {
            // A bound beyond `i128` (the maximum of `u128`) bounds no literal.
            let below_max = match max.kind {
                ExprKindGenData::Const(ConstData::Int(max)) => {
                    i128::try_from(*max).ok().is_none_or(|max| v <= max)
                }
                _ => false,
            };
            as_int(min.as_dyn()).is_some_and(|min| min <= v) && below_max
        };
        (inner.target == inverse.inner.to_str() && inverse.ranges.iter().any(in_range))
            .then(|| self.node_of_kind(self.orig.unwrap(), k.kind))
    }

    /// `forall xs :: b` and `exists xs :: b` for a literal `b` are `b`:
    /// Viper's types are inhabited.
    fn fold_quantifier(&mut self, body: ExprDyn<'vir>) -> Option<ExprDyn<'vir>> {
        as_bool(body).map(|b| self.bool(b))
    }

    /// Follows locals to their bound values, to match patterns through them.
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

    // The constructors for results. A node built here takes the span and
    // debug information of the node being rewritten.

    fn node(&self, kind: ExprKindGenData<'vir, (), !>) -> ExprDyn<'vir> {
        self.node_at(self.orig.expect("a node is being rewritten"), kind)
    }

    fn build(&mut self, kind: ExprKindGenData<'vir, (), !>) -> ExprDyn<'vir> {
        let e = self.node(kind);
        self.fold(e).unwrap_or(e)
    }

    fn bool(&self, b: bool) -> ExprDyn<'vir> {
        self.node(ExprKindGenData::Const(self.vcx.alloc(ConstData::Bool(b))))
    }

    fn not(&mut self, e: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.build(ExprKindGenData::UnOp(self.vcx.alloc(UnOpGenData {
            kind: UnOpKind::Not,
            expr: e.inner_cast_ty(),
        })))
    }

    fn bin_op(&mut self, kind: BinOpKind, lhs: ExprDyn<'vir>, rhs: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.build(ExprKindGenData::BinOp(self.vcx.alloc(BinOpGenData {
            kind,
            lhs,
            rhs,
        })))
    }

    fn ternary(&mut self, c: ExprDyn<'vir>, a: ExprDyn<'vir>, b: ExprDyn<'vir>) -> ExprDyn<'vir> {
        self.build(ExprKindGenData::Ternary(self.vcx.alloc(TernaryGenData {
            cond: c.inner_cast_ty(),
            then: a,
            else_: b,
        })))
    }

    /// The application `app` to other arguments.
    fn app(
        &mut self,
        app: &'vir FuncAppGenData<'vir, (), !>,
        args: &[ExprDyn<'vir>],
    ) -> ExprDyn<'vir> {
        self.build(ExprKindGenData::FuncApp(self.vcx.alloc(FuncAppGenData {
            args: self.vcx.alloc_slice(args),
            ..*app
        })))
    }
}

fn as_bool(e: ExprDyn<'_>) -> Option<bool> {
    match e.kind {
        ExprKindGenData::Const(ConstData::Bool(b)) => Some(*b),
        _ => None,
    }
}

/// An integer literal, a negative one written as the negation of its
/// absolute value; `None` beyond `i128`.
pub(super) fn as_int(e: ExprDyn<'_>) -> Option<i128> {
    match e.kind {
        ExprKindGenData::Const(ConstData::Int(v)) => i128::try_from(*v).ok(),
        ExprKindGenData::UnOp(u) if u.kind == UnOpKind::Neg => match u.expr.kind {
            ExprKindGenData::Const(ConstData::Int(v)) => 0i128.checked_sub_unsigned(*v),
            _ => None,
        },
        _ => None,
    }
}

/// Whether two applications have the same target, type arguments and number
/// and types of arguments.
fn same_arg_types(x: &FuncAppGenData<'_, (), !>, y: &FuncAppGenData<'_, (), !>) -> bool {
    x.target == y.target
        && x.typ_var_map == y.typ_var_map
        && x.args.len() == y.args.len()
        && x.args.iter().zip(y.args).all(|(a, b)| a.ty() == b.ty())
}

/// Syntactic equality of the expressions the equations compare (locals,
/// constants, applications and field reads), `false` for anything else.
fn syntactic_eq<'vir>(a: ExprDyn<'vir>, b: ExprDyn<'vir>) -> bool {
    if std::ptr::eq(a.kind, b.kind) {
        return true;
    }
    match (a.kind, b.kind) {
        (ExprKindGenData::Local(x), ExprKindGenData::Local(y)) => x.name == y.name,
        (ExprKindGenData::Const(x), ExprKindGenData::Const(y)) => x == y,
        (ExprKindGenData::FuncApp(x), ExprKindGenData::FuncApp(y)) => {
            same_arg_types(x, y)
                && x.result_ty == y.result_ty
                && x.args.iter().zip(y.args).all(|(a, b)| syntactic_eq(a, b))
        }
        (ExprKindGenData::AdtDestructor(r1, d1), ExprKindGenData::AdtDestructor(r2, d2)) => {
            d1.name == d2.name && syntactic_eq(r1, r2)
        }
        _ => false,
    }
}
