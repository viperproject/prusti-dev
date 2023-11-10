use crate::VirCtxt;
use crate::gendata::*;
use crate::genrefs::*;
use crate::refs::*;

pub use vir_proc_macro::*;

pub trait Reify<'vir, Curr> {
    type Next: Sized;

    fn reify<'tcx>(
        &self,
        vcx: &'vir VirCtxt<'tcx>,
        lctx: Curr,
    ) -> Self::Next;
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>
{
    type Next = ExprGen<'vir, NextA, NextB>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        match self {
            ExprGenData::Field(v, f) => vcx.alloc(ExprGenData::Field(v.reify(vcx, lctx), f)),
            ExprGenData::Old(v) => vcx.alloc(ExprGenData::Old(v.reify(vcx, lctx))),
            ExprGenData::AccField(v) => vcx.alloc(ExprGenData::AccField(v.reify(vcx, lctx))),
            ExprGenData::Unfolding(v) => vcx.alloc(ExprGenData::Unfolding(v.reify(vcx, lctx))),
            ExprGenData::UnOp(v) => vcx.alloc(ExprGenData::UnOp(v.reify(vcx, lctx))),
            ExprGenData::BinOp(v) => vcx.alloc(ExprGenData::BinOp(v.reify(vcx, lctx))),
            ExprGenData::Ternary(v) => vcx.alloc(ExprGenData::Ternary(v.reify(vcx, lctx))),
            ExprGenData::Forall(v) => vcx.alloc(ExprGenData::Forall(v.reify(vcx, lctx))),
            ExprGenData::Let(v) => vcx.alloc(ExprGenData::Let(v.reify(vcx, lctx))),
            ExprGenData::FuncApp(v) => vcx.alloc(ExprGenData::FuncApp(v.reify(vcx, lctx))),
            ExprGenData::PredicateApp(v) => vcx.alloc(ExprGenData::PredicateApp(v.reify(vcx, lctx))),

            ExprGenData::Local(v) => vcx.alloc(ExprGenData::Local(v)),
            ExprGenData::Const(v) => vcx.alloc(ExprGenData::Const(v)),
            ExprGenData::Todo(v) => vcx.alloc(ExprGenData::Todo(v)),

            ExprGenData::Lazy(_, f) => f(vcx, lctx),
        }
    }
}

// TODO: how to make these generic? i.e. how to implement `Reify` for *any*
//   slice of reify-able elements? same for an Option of a slice;
//   for now these implementations are generated in the Reify derive macro

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]
{
    type Next = &'vir [ExprGen<'vir, NextA, NextB>];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|elem| elem.reify(vcx, lctx))
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [&'vir [ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]]
{
    type Next = &'vir [&'vir [ExprGen<'vir, NextA, NextB>]];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|elem| elem.reify(vcx, lctx))
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [(ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>, CfgBlockLabel<'vir>)]
{
    type Next = &'vir [(ExprGen<'vir, NextA, NextB>, CfgBlockLabel<'vir>)];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|(elem, label)| (elem.reify(vcx, lctx), *label))
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for Option<ExprGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>>
{
    type Next = Option<ExprGen<'vir, NextA, NextB>>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        self.map(|elem| elem.reify(vcx, lctx))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for Option<&'vir [CfgBlockGen<'vir, Curr, ExprGen<'vir, NextA, NextB>>]>
{
    type Next = Option<&'vir [CfgBlockGen<'vir, NextA, NextB>]>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        self.map(|elem| elem.reify(vcx, lctx))
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
