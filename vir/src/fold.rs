use crate::{gendata::*, genrefs::*, CastType, CompType};

/// A rewrite of the expressions in VIR data, the counterpart of
/// [`crate::Visitor`] in the style of rustc's `TypeFolder`:
/// [`Foldable::fold_with`] hands each expression to [`Self::fold_expr`], whose
/// default folds its subexpressions with [`ExprGenData::super_fold_with`]. An
/// override calls that itself to continue. Magic wands, wherever they occur,
/// are handed to [`Self::fold_wand`] likewise. `None` stands for unchanged
/// data, so that it is never reallocated.
pub trait Folder<'vir, Curr, Next> {
    fn fold_expr(
        &mut self,
        e: ExprGenDyn<'vir, Curr, Next>,
    ) -> Option<ExprGenDyn<'vir, Curr, Next>> {
        e.super_fold_with(self)
    }

    fn fold_wand(&mut self, w: WandGen<'vir, Curr, Next>) -> Option<WandGen<'vir, Curr, Next>> {
        w.super_fold_with(self)
    }
}

/// VIR data containing expressions, in the style of rustc's
/// `TypeFoldable`: an expression is handed to the folder, other data folds
/// each expression it is made of. Derived with `VirFoldable` for the generic
/// VIR data (folding the fields `VirReify` descends into). Returns `None` if
/// nothing changed.
pub trait Foldable<'vir, Curr, Next>: Sized {
    fn fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self>;
}

impl<'vir, Curr, Next, T: CompType> ExprGenData<'vir, Curr, Next, T> {
    /// Folds the subexpressions of this expression.
    pub fn super_fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(
        &'vir self,
        f: &mut F,
    ) -> Option<&'vir Self> {
        let kind = self.kind.fold_with(f)?;
        Some(crate::with_vcx(|vcx| {
            vcx.alloc(Self::new_inner(kind, self.debug_info, self.span, self.ty()))
        }))
    }
}

impl<'vir, Curr, Next, T: CompType> Foldable<'vir, Curr, Next>
    for &'vir ExprGenData<'vir, Curr, Next, T>
{
    fn fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self> {
        f.fold_expr((*self).as_dyn()).map(|e| e.inner_cast_ty())
    }
}

impl<'vir, Curr, Next> WandGenData<'vir, Curr, Next> {
    /// Folds the sides of this magic wand.
    pub fn super_fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(
        &'vir self,
        f: &mut F,
    ) -> Option<&'vir Self> {
        let lhs = self.lhs.fold_with(f);
        let rhs = self.rhs.fold_with(f);
        if lhs.is_none() && rhs.is_none() {
            return None;
        }
        Some(crate::with_vcx(|vcx| {
            vcx.alloc(WandGenData {
                lhs: lhs.unwrap_or(self.lhs),
                rhs: rhs.unwrap_or(self.rhs),
            })
        }))
    }
}

impl<'vir, Curr, Next> Foldable<'vir, Curr, Next> for &'vir WandGenData<'vir, Curr, Next> {
    fn fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self> {
        f.fold_wand(self)
    }
}

impl<'vir, Curr, Next, X: Foldable<'vir, Curr, Next> + Copy> Foldable<'vir, Curr, Next>
    for &'vir [X]
{
    fn fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self> {
        let folded = self
            .iter()
            .map(|elem| elem.fold_with(f))
            .collect::<Vec<_>>();
        if folded.iter().all(Option::is_none) {
            return None;
        }
        let elems = folded
            .into_iter()
            .zip(self.iter())
            .map(|(new, old)| new.unwrap_or(*old))
            .collect::<Vec<_>>();
        Some(crate::with_vcx(|vcx| vcx.alloc_slice(&elems)))
    }
}

impl<'vir, Curr, Next, X: Foldable<'vir, Curr, Next>> Foldable<'vir, Curr, Next> for Option<X> {
    fn fold_with<F: Folder<'vir, Curr, Next> + ?Sized>(&self, f: &mut F) -> Option<Self> {
        self.as_ref()?.fold_with(f).map(Some)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::BinOpKind;

    /// Replaces the local `x` by `y`.
    struct Rename;
    impl<'vir> Folder<'vir, (), !> for Rename {
        fn fold_expr(&mut self, e: ExprGenDyn<'vir, (), !>) -> Option<ExprGenDyn<'vir, (), !>> {
            match e.kind {
                ExprKindGenData::Local(l) if l.name == "x" => Some(crate::with_vcx(|vcx| {
                    vcx.mk_local_ex(vcx.mk_local_decl("y", crate::TYPE_INT))
                        .as_dyn()
                })),
                _ => e.super_fold_with(self),
            }
        }
    }

    #[test]
    fn reallocates_only_changed_data() {
        crate::init_vcx(crate::VirCtxt::new_without_tcx());
        crate::with_vcx(|vcx| {
            let ex = |name| vcx.mk_local_ex::<(), !, _>(vcx.mk_local_decl(name, crate::TYPE_INT));
            let unchanged = vcx.mk_eq_expr(ex("z"), ex("y"));
            let changed = vcx.mk_eq_expr(ex("x"), ex("z"));
            let e = vcx
                .mk_bin_op_expr(BinOpKind::And, changed, unchanged)
                .as_dyn();
            let folded = e.fold_with(&mut Rename).unwrap();
            assert_eq!(format!("{folded:?}"), "((y) == (z)) && ((z) == (y))");
            let ExprKindGenData::BinOp(b) = folded.kind else {
                panic!("expected a binary operation");
            };
            assert!(std::ptr::eq(b.rhs, unchanged.as_dyn()));
            assert!(unchanged.as_dyn().fold_with(&mut Rename).is_none());
        });
    }
}
