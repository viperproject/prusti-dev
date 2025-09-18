use std::cell::RefCell;

use prusti_interface::specs::{
    specifications::SpecQuery,
    typed::{DefSpecificationMap, ProcedureSpecification, SpecificationItem},
};
use prusti_rustc_interface::{
    middle::ty,
    span::def_id::DefId,
};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

pub struct SpecEnc;

pub type SpecEncError = ();

#[derive(Clone, Debug)]
pub struct SpecEncOutput<'vir> {
    //pub expr: vir::Expr<'vir>,
    pub pres: &'vir [DefId],
    pub posts: &'vir [DefId],
    pub pledges: &'vir [(Option<DefId>, DefId)], // TODO: reuse Pledge type?
}

thread_local! {
    static DEF_SPEC_MAP: RefCell<Option<DefSpecificationMap>> = RefCell::new(Default::default());
}

pub fn with_type_spec<F, R>(f: F) -> R
where
    F: FnOnce(&DefSpecificationMap) -> R,
{
    vir::with_vcx(|vcx| f(vcx.specs.as_ref().unwrap().borrow().get_type_specs()))
}

pub fn with_proc_spec<'tcx, F, R>(query: SpecQuery<'tcx>, f: F) -> Option<R>
where
    F: FnOnce(&ProcedureSpecification) -> R,
{
    vir::with_vcx(|vcx| {
        let specs = vcx.specs.as_ref().unwrap();
        specs
            .borrow_mut()
            .get_and_refine_proc_spec(vcx.tcx(), query)
            .map(f)
    })
}

pub fn is_function_trusted(def_id: DefId) -> bool {
    let substs = ty::GenericArgs::identity_for_item(vir::with_vcx(|vcx| vcx.tcx()), def_id);
    with_proc_spec(
        SpecQuery::GetProcKind(def_id, substs),
        |proc_spec: &ProcedureSpecification| {
            proc_spec.trusted.extract_inherit().unwrap_or_default()
        },
    )
    .unwrap_or_default()
}

pub fn is_type_trusted(ty: ty::Ty) -> bool {
    match ty.kind() {
        prusti_rustc_interface::middle::ty::TyKind::Adt(adt_def, _) => with_type_spec(|def_spec| {
            def_spec
                .get_type_spec(&adt_def.did())
                .map(|type_spec| type_spec.trusted.extract_inherit().unwrap_or_default())
                .unwrap_or_default()
        }),
        _ => false,
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct SpecEncTask {
    pub def_id: DefId, // ID of the function
                       // TODO: substs here?
}

impl TaskEncoder for SpecEnc {
    task_encoder::encoder_cache!(SpecEnc);

    type TaskDescription<'vir> = SpecEncTask;

    type TaskKey<'vir> = (
        DefId, // ID of the function
    );

    type OutputFullDependency<'vir> = SpecEncOutput<'vir>;

    type EncodingError = SpecEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        (
            // TODO
            task.def_id,
        )
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let (pres, posts, pledges) = with_proc_spec(
                SpecQuery::GetProcKind(
                    task_key.0,
                    ty::List::identity_for_item(vcx.tcx(), task_key.0),
                ),
                |specs| {
                    // TODO: handle specs other than `empty_or_inherent`
                    let pres = get_spec_items(vcx, &specs.pres);
                    let posts = get_spec_items(vcx, &specs.posts);
                    let pledges = get_spec_items(vcx, &specs.pledges);
                    (pres, posts, pledges)
                },
            )
            .unwrap_or((&[], &[], &[]));
            let pledges = vcx.alloc_slice(
                &pledges
                    .iter()
                    .map(|pledge| (pledge.lhs, pledge.rhs))
                    .collect::<Vec<_>>(),
            );
            Ok(((), SpecEncOutput { pres, posts, pledges }))
        })
    }
}

fn get_spec_items<'vir, T: Copy>(
    vcx: &'vir VirCtxt<'_>,
    spec: &SpecificationItem<Vec<T>>,
) -> &'vir [T] {
    match spec {
        SpecificationItem::Inherent(items) | SpecificationItem::Inherited(items) => {
            vcx.alloc_slice(items)
        }
        SpecificationItem::Empty => &[],
        _ => todo!(),
    }
}
