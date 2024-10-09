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
    for ExprGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>> {
    type Next = ExprGen<'vir, NextA, NextB>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc(ExprGenData {
            kind: self.kind.reify(vcx, lctx),
            debug_info: self.debug_info,
            span: self.span,
        })
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for ExprKindGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>
{
    type Next = ExprKindGen<'vir, NextA, NextB>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        match self {
            ExprKindGenData::Field(v, f) => vcx.alloc(ExprKindGenData::Field(v.reify(vcx, lctx), f)),
            ExprKindGenData::Old(v) => vcx.alloc(ExprKindGenData::Old(v.reify(vcx, lctx))),
            ExprKindGenData::AccField(v) => vcx.alloc(ExprKindGenData::AccField(v.reify(vcx, lctx))),
            ExprKindGenData::Unfolding(v) => vcx.alloc(ExprKindGenData::Unfolding(v.reify(vcx, lctx))),
            ExprKindGenData::UnOp(v) => vcx.alloc(ExprKindGenData::UnOp(v.reify(vcx, lctx))),
            ExprKindGenData::BinOp(v) => vcx.alloc(ExprKindGenData::BinOp(v.reify(vcx, lctx))),
            ExprKindGenData::Ternary(v) => vcx.alloc(ExprKindGenData::Ternary(v.reify(vcx, lctx))),
            ExprKindGenData::Forall(v) => vcx.alloc(ExprKindGenData::Forall(v.reify(vcx, lctx))),
            ExprKindGenData::Exists(v) => vcx.alloc(ExprKindGenData::Exists(v.reify(vcx, lctx))),
            ExprKindGenData::Let(v) => vcx.alloc(ExprKindGenData::Let(v.reify(vcx, lctx))),
            ExprKindGenData::FuncApp(v) => vcx.alloc(ExprKindGenData::FuncApp(v.reify(vcx, lctx))),
            ExprKindGenData::PredicateApp(v) => vcx.alloc(ExprKindGenData::PredicateApp(v.reify(vcx, lctx))),

            ExprKindGenData::Local(v) => vcx.alloc(ExprKindGenData::Local(v)),
            ExprKindGenData::Const(v) => vcx.alloc(ExprKindGenData::Const(v)),
            ExprKindGenData::Result(t) => vcx.alloc(ExprKindGenData::Result(t)),
            ExprKindGenData::Todo(v) => vcx.alloc(ExprKindGenData::Todo(v)),

            ExprKindGenData::Lazy(v) => (v.func)(vcx, lctx),
        }
    }
}


// TODO: how to make these generic? i.e. how to implement `Reify` for *any*
//   slice of reify-able elements? same for an Option of a slice;
//   for now these implementations are generated in the Reify derive macro

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [ExprGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>]
{
    type Next = &'vir [ExprGen<'vir, NextA, NextB>];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|elem| elem.reify(vcx, lctx))
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [&'vir [ExprGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>]]
{
    type Next = &'vir [&'vir [ExprGen<'vir, NextA, NextB>]];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|elem| elem.reify(vcx, lctx))
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for [(
        ExprGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>,
        CfgBlockLabel<'vir>,
        &'vir [StmtGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>],
    )]
{
    type Next = &'vir [(
        ExprGen<'vir, NextA, NextB>,
        CfgBlockLabel<'vir>,
        &'vir [StmtGen<'vir, NextA, NextB>],
    )];
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        vcx.alloc_slice(&self.iter()
            .map(|(elem, label, extra_exprs)| {
                (elem.reify(vcx, lctx), *label, extra_exprs.reify(vcx, lctx))
            })
            .collect::<Vec<_>>())
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for Option<ExprGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>>
{
    type Next = Option<ExprGen<'vir, NextA, NextB>>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        self.map(|elem| elem.reify(vcx, lctx))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for Option<&'vir [CfgBlockGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>]>
{
    type Next = Option<&'vir [CfgBlockGen<'vir, NextA, NextB>]>;
    fn reify<'tcx>(&self, vcx: &'vir VirCtxt<'tcx>, lctx: Curr) -> Self::Next {
        self.map(|elem| elem.reify(vcx, lctx))
    }
}

impl<'vir, Curr: Copy, NextA, NextB> Reify<'vir, Curr>
    for Option<MethodBodyGen<'vir, Curr, ExprKindGen<'vir, NextA, NextB>>>
{
    type Next = Option<MethodBodyGen<'vir, NextA, NextB>>;
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
