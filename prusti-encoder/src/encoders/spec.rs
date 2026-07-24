use std::cell::RefCell;

use prusti_interface::specs::{
    specifications::SpecQuery,
    typed::{
        self, DefSpecificationMap, ExternSpecKind, Pledge, ProcedureSpecification,
        SpecificationItem,
    },
};
use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::VirCtxt;

use crate::encoders::ty::generics::GArgs;

pub struct SpecEnc;

pub type SpecEncError = ();

#[derive(Clone, Debug)]
pub struct SpecEncOutput<'vir> {
    pub extern_spec: Option<ExternSpecKind>,
    pub pres: &'vir [DefId],
    pub posts: &'vir [DefId],
    pub pledges: &'vir [Pledge],
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

pub fn is_function_pure<'tcx>(def_id: DefId, args: GArgs<'tcx>) -> bool {
    with_proc_spec(
        SpecQuery::GetProcKind(def_id, args.args()),
        |proc_spec: &ProcedureSpecification| kind_is_pure(&proc_spec.kind),
    )
    .unwrap_or_default()
}

/// `kind.is_pure()`, treating an invalid trait-to-impl kind refinement as
/// impure. This is a pure query; the refinement error itself is reported to
/// the user separately by [`report_kind_refinement_error`].
pub fn kind_is_pure(kind: &SpecificationItem<typed::ProcedureSpecificationKind>) -> bool {
    kind.is_pure().unwrap_or(false)
}

/// Emit a user error for an invalid trait-to-impl kind refinement (e.g. an
/// `impl` of a `#[pure]` trait method that is not itself `#[pure]`); a no-op if
/// the refinement is valid. Kept separate from the purity query so it can be
/// called once per function, at encoding time, rather than on every query.
pub fn report_kind_refinement_error(
    def_id: DefId,
    kind: &SpecificationItem<typed::ProcedureSpecificationKind>,
) {
    use typed::ProcedureSpecificationKind::*;
    let Err(typed::ProcedureSpecificationKindError::InvalidSpecKindRefinement(base, refined)) =
        kind.is_pure()
    else {
        return;
    };
    vir::with_vcx(|vcx| {
        let name = vcx.tcx().def_path_str(def_id);
        let span = vcx.tcx().def_span(def_id).into();
        let error = match (base, refined) {
            (Pure, Impure) => {
                let mut error = prusti_interface::PrustiError::incorrect(
                    format!("`{name}` implements a `#[pure]` trait method and so must itself be `#[pure]`"),
                    span,
                )
                .set_help("add `#[pure]` to the implementation");
                // Point at the `#[pure]` in the trait definition (its
                // `specs_version` marker is spanned at the annotation), when
                // the trait method is available locally.
                if let Some(trait_item) = vcx
                    .tcx()
                    .opt_associated_item(def_id)
                    .and_then(|item| item.trait_item_def_id)
                {
                    let trait_attrs = vcx.tcx().get_all_attrs(trait_item);
                    if let Some(pure_span) =
                        prusti_interface::utils::prusti_attr_span(trait_attrs, "pure")
                    {
                        error = error.add_note(
                            "the trait method is declared `#[pure]` here",
                            Some(pure_span),
                        );
                    }
                }
                error
            }
            _ => prusti_interface::PrustiError::incorrect(
                format!("the specification of `{name}` is incompatible with the trait declaration"),
                span,
            ),
        };
        vcx.emit_early_error(error);
    });
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
    const ENCODER_NAME: &'static str = "spec encoder";

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
            let (extern_spec, pres, posts, pledges) = with_proc_spec(
                SpecQuery::GetProcKind(
                    task_key.0,
                    ty::List::identity_for_item(vcx.tcx(), task_key.0),
                ),
                |specs| {
                    // TODO: handle specs other than `empty_or_inherent`
                    let pres = get_spec_items(vcx, &specs.pres);
                    let posts = get_spec_items(vcx, &specs.posts);
                    let pledges = get_spec_items(vcx, &specs.pledges);
                    (specs.extern_spec, pres, posts, pledges)
                },
            )
            .unwrap_or((None, &[], &[], &[]));
            let pledges = vcx.alloc_slice(
                &pledges
                    .iter()
                    .map(|pledge| Pledge::new(pledge.lhs, pledge.rhs))
                    .collect::<Vec<_>>(),
            );
            Ok((
                (),
                SpecEncOutput {
                    extern_spec,
                    pres,
                    posts,
                    pledges,
                },
            ))
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
        SpecificationItem::Refined(_from, to) => {
            // Here we ignore the original specs: to get to this branch, the
            // task key given to `SpecEnc` was the `DefId` of an trait method
            // implementation, which will happen when encoding the definition
            // of that implementation.
            //
            // At callsites, `MethodCallEnc` will direct the call to the stub
            // method, which uses the `DefId` of the trait item for emitting
            // its specifications.
            vcx.alloc_slice(to)
        }
    }
}
