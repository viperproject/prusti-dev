use crate::VirCtxt;
use crate::gendata::*;
use crate::genrefs::*;
use crate::refs::*;

pub use vir_proc_macro::*;

pub trait Reify<'vir, Curr, NextA, NextB> {
    type Next: Sized;

    fn reify(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        lctx: Curr,
    ) -> Self::Next;

    /// Returns `Some` only if a `Lazy` was called anywhere.
    fn reify_deep(
        &self,
        vcx: &'vir VirCtxt<'vir>,
        lctx: Curr,
    ) -> Option<Self::Next>;
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>
{
    type Next = ExprGen<'vir, NextA, NextB>;
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        Some(match self {
            ExprGenData::Field(v, f) => vcx.alloc(ExprGenData::Field(v.reify_deep(vcx, lctx)?, f)),
            ExprGenData::Old(v) => vcx.alloc(ExprGenData::Old(v.reify_deep(vcx, lctx)?)),
            ExprGenData::AccField(v) => vcx.alloc(ExprGenData::AccField(v.reify_deep(vcx, lctx)?)),
            ExprGenData::Unfolding(v) => vcx.alloc(ExprGenData::Unfolding(v.reify_deep(vcx, lctx)?)),
            ExprGenData::UnOp(v) => vcx.alloc(ExprGenData::UnOp(v.reify_deep(vcx, lctx)?)),
            ExprGenData::BinOp(v) => vcx.alloc(ExprGenData::BinOp(v.reify_deep(vcx, lctx)?)),
            ExprGenData::Ternary(v) => vcx.alloc(ExprGenData::Ternary(v.reify_deep(vcx, lctx)?)),
            ExprGenData::Forall(v) => vcx.alloc(ExprGenData::Forall(v.reify_deep(vcx, lctx)?)),
            ExprGenData::Let(v) => vcx.alloc(ExprGenData::Let(v.reify_deep(vcx, lctx)?)),
            ExprGenData::FuncApp(v) => vcx.alloc(ExprGenData::FuncApp(v.reify_deep(vcx, lctx)?)),
            ExprGenData::PredicateApp(v) => vcx.alloc(ExprGenData::PredicateApp(v.reify_deep(vcx, lctx)?)),

            ExprGenData::Lazy(_, f) => f(vcx, lctx),
            _ => return None,
        })
    }
}

// TODO: how to make these generic? i.e. how to implement `Reify` for *any*
//   slice of reify-able elements? same for an Option of a slice;
//   for now these implementations are generated in the Reify derive macro

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for [ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]
{
    type Next = &'vir [ExprGen<'vir, NextA, NextB>];
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        let mut any_change = false;
        let vals = self.iter()
            .map(|elem| {
                let elem = elem.reify_deep(vcx, lctx);
                any_change |= elem.is_some();
                elem
            })
            .collect::<Vec<Option<_>>>();
        if !any_change {
            return None;
        };
        Some(vcx.alloc_slice(&vals.into_iter()
            .map(|elem| elem.unwrap_or_else(|| unsafe { std::mem::transmute(elem) }))
            .collect::<Vec<_>>()))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for [&'vir [ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]]
{
    type Next = &'vir [&'vir [ExprGen<'vir, NextA, NextB>]];
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        let mut any_change = false;
        let vals = self.iter()
            .map(|elem| {
                let elem = elem.reify_deep(vcx, lctx);
                any_change |= elem.is_some();
                elem
            })
            .collect::<Vec<Option<_>>>();
        if !any_change {
            return None;
        };
        Some(vcx.alloc_slice(&vals.into_iter()
            .map(|elem| elem.unwrap_or_else(|| unsafe { std::mem::transmute(elem) }))
            .collect::<Vec<_>>()))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for [(ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>, CfgBlockLabel<'vir>)]
{
    type Next = &'vir [(ExprGen<'vir, NextA, NextB>, CfgBlockLabel<'vir>)];
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        let mut any_change = false;
        let vals = self.iter()
            .map(|(elem, label)| {
                let elem = elem.reify_deep(vcx, lctx);
                any_change |= elem.is_some();
                (elem, label)
            })
            .collect::<Vec<_>>();
        if !any_change {
            return None;
        };
        Some(vcx.alloc_slice(&vals.into_iter()
            .map(|(elem, label)| (
                elem.unwrap_or_else(|| unsafe { std::mem::transmute(elem) }),
                *label,
            ))
            .collect::<Vec<_>>()))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for Option<ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>>
{
    type Next = Option<ExprGen<'vir, NextA, NextB>>;
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        match self {
            // there was an expression, does it need reification?
            Some(elem) => Some(Some(elem.reify_deep(vcx, lctx)?)),
            // there was nothing inside, there is no reification to perform
            None => None,
        }
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr, NextA, NextB>
    for Option<&'vir [CfgBlockGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]>
{
    type Next = Option<&'vir [CfgBlockGen<'vir, NextA, NextB>]>;
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(*self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        match self {
            // there was an expression, does it need reification?
            Some(elem) => Some(Some(elem.reify_deep(vcx, lctx)?)),
            // there was nothing inside, there is no reification to perform
            None => None,
        }
    }
}


/*
impl<
    'vir,
    Curr: Copy, NextA, NextB,
    Elem: Reify<'vir, Curr, NextA, NextB>,
> Reify<'vir, Curr, NextA, NextB>
    for [&'vir Elem]
where
    <Elem as Reify<'vir, Curr, NextA, NextB>>::Next: 'vir
{
    type Next = &'vir [<Elem as Reify<'vir, Curr, NextA, NextB>>::Next];
    fn reify(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Self::Next {
        self.reify_deep(vcx, lctx)
            .unwrap_or_else(|| unsafe { std::mem::transmute(self) })
    }
    fn reify_deep(&self, vcx: &'vir VirCtxt<'vir>, lctx: Curr) -> Option<Self::Next> {
        Some(vcx.alloc_slice(&self.iter()
            .map(|elem| elem.reify_deep(vcx, lctx))
            .collect::<Option<Vec<_>>>()?))
    }
}
*/
