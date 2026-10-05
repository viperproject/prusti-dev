use prusti_rustc_interface::data_structures::fx::FxHashSet;

use crate::{gendata::*, genrefs::*, CastType, CompType};

/// A walk over the expressions in VIR data, in the style of rustc's
/// `TypeVisitor`: [`Visitable::visit_with`] hands each expression to
/// [`Self::visit_expr`], whose default continues into its subexpressions
/// with [`ExprGenData::super_visit_with`]. An override calls that itself to
/// continue.
pub trait Visitor<'vir, Curr, Next> {
    fn visit_expr(&mut self, e: ExprGenDyn<'vir, Curr, Next>) {
        e.super_visit_with(self);
    }
}

/// VIR data containing expressions, in the style of rustc's
/// `TypeVisitable`: an expression is handed to the visitor, other data
/// visits each expression it is made of. Derived with `VirVisitable` for the
/// generic VIR data (visiting the fields `VirReify` descends into).
pub trait Visitable<'vir, Curr, Next> {
    fn visit_with<V: Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V);
}

impl<'vir, Curr, Next, T: CompType> ExprGenData<'vir, Curr, Next, T> {
    /// Visits the subexpressions of this expression.
    pub fn super_visit_with<V: Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V) {
        self.kind.visit_with(v);
    }
}

impl<'vir, Curr, Next, T: CompType> Visitable<'vir, Curr, Next>
    for &'vir ExprGenData<'vir, Curr, Next, T>
{
    fn visit_with<V: Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V) {
        v.visit_expr((*self).as_dyn());
    }
}

impl<'vir, Curr, Next, X: Visitable<'vir, Curr, Next>> Visitable<'vir, Curr, Next> for [X] {
    fn visit_with<V: Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V) {
        for elem in self {
            elem.visit_with(v);
        }
    }
}

impl<'vir, Curr, Next, X: Visitable<'vir, Curr, Next>> Visitable<'vir, Curr, Next> for Option<X> {
    fn visit_with<V: Visitor<'vir, Curr, Next> + ?Sized>(&self, v: &mut V) {
        if let Some(elem) = self {
            elem.visit_with(v);
        }
    }
}

/// Collects every local name occurring in `e` (a superset of its free
/// locals: bound variables of quantifiers and lets are included).
pub fn collect_locals<'vir, Curr, Next>(
    e: ExprGenDyn<'vir, Curr, Next>,
    out: &mut FxHashSet<&'vir str>,
) {
    struct Locals<'a, 'vir>(&'a mut FxHashSet<&'vir str>);
    impl<'vir, Curr, Next> Visitor<'vir, Curr, Next> for Locals<'_, 'vir> {
        fn visit_expr(&mut self, e: ExprGenDyn<'vir, Curr, Next>) {
            if let ExprKindGenData::Local(local) = e.kind {
                self.0.insert(local.name);
            }
            e.super_visit_with(self);
        }
    }
    e.visit_with(&mut Locals(out));
}

#[cfg(test)]
mod tests {
    use super::*;

    /// `forall x :: {old(t)} let y == z in (t == x ? y : x) == x`
    fn sample<'vir>(vcx: &'vir crate::VirCtxt<'_>) -> ExprGenDyn<'vir, (), !> {
        let decl = |name| vcx.mk_local_decl(name, crate::TYPE_INT);
        let (x, y, z, t) = (decl("x"), decl("y"), decl("z"), decl("t"));
        let ex = |decl| vcx.mk_local_ex::<(), !, _>(decl);
        let trigger = vcx.mk_trigger(&[vcx.mk_old_expr(ex(t))]);
        let cond = vcx.mk_eq_expr(ex(t), ex(x));
        let let_ = vcx.mk_let_expr(y, ex(z), vcx.mk_ternary_expr(cond, ex(y), ex(x)));
        let body = vcx.mk_eq_expr(let_, ex(x));
        vcx.mk_forall_expr(vcx.alloc_slice(&[x]), vcx.alloc_slice(&[trigger]), body)
            .as_dyn()
    }

    #[test]
    fn collects_locals_in_binders_and_triggers() {
        crate::init_vcx(crate::VirCtxt::new_without_tcx());
        crate::with_vcx(|vcx| {
            let mut locals = FxHashSet::default();
            collect_locals(sample(vcx), &mut locals);
            assert_eq!(locals, FxHashSet::from_iter(["x", "y", "z", "t"]));
        });
    }

    #[test]
    fn visits_every_subexpression() {
        struct Count(usize);
        impl<'vir> Visitor<'vir, (), !> for Count {
            fn visit_expr(&mut self, e: ExprGenDyn<'vir, (), !>) {
                self.0 += 1;
                e.super_visit_with(self);
            }
        }
        crate::init_vcx(crate::VirCtxt::new_without_tcx());
        crate::with_vcx(|vcx| {
            let mut count = Count(0);
            sample(vcx).visit_with(&mut count);
            // forall; old, t; ==, let, z, ternary, ==, t, x, y, x, x
            assert_eq!(count.0, 13);
        });
    }
}
