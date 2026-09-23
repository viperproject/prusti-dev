use std::cell::RefCell;

use prusti_interface::{
    environment::EnvQuery,
    specs::{
        specifications::SpecQuery,
        typed::{
            self, DefSpecificationMap, ExternSpecKind, Pledge, ProcedureSpecification,
            SpecificationItem,
        },
    },
};
use prusti_rustc_interface::{hir, middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use crate::encoders::ty::generics::GArgs;

pub struct SpecEnc;

pub type SpecEncError = ();

#[derive(Clone, Debug)]
pub struct SpecEncOutput<'vir> {
    pub extern_spec: Option<ExternSpecKind>,
    pub pres: SpecificationItem<&'vir [DefId]>,
    pub posts: SpecificationItem<&'vir [DefId]>,
    pub pledges: SpecificationItem<&'vir [Pledge]>,
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

/// Whether a function's spec is trusted -- assumed rather than verified. This
/// holds if the function itself is marked `#[trusted]` (never inherited; see
/// `ProcedureSpecification::refine`), or if the spec derives from an
/// `#[extern_spec]` and the function is foreign: such specs are always
/// assumed (the mandatory `#[trusted]` inside the extern spec covers them).
/// In particular a foreign impl inheriting the spec of an extern-spec'd trait
/// method is assumed, necessarily: the annotation postdates the compilation
/// of the defining crate (or that crate is not compiled by Prusti at all,
/// e.g. `std`), so no body for it can ever have been exported. A *local* impl
/// of such a trait has a body and is verified.
pub fn spec_is_trusted(proc_spec: &ProcedureSpecification, def_id: DefId) -> bool {
    let user_trusted = proc_spec
        .trusted
        .extract_with_selective_replacement()
        .copied()
        .unwrap_or_default();
    let extern_trusted = proc_spec.extern_spec.is_some() && !def_id.is_local();
    user_trusted || extern_trusted
}

pub fn is_function_trusted(def_id: DefId) -> bool {
    let substs = ty::GenericArgs::identity_for_item(vir::with_vcx(|vcx| vcx.tcx()), def_id);
    with_proc_spec(
        SpecQuery::GetProcKind(def_id, substs),
        |proc_spec: &ProcedureSpecification| spec_is_trusted(proc_spec, def_id),
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

/// The function carrying the contract of dropping a value of type `ty`
/// (from `#[extern_spec] impl Drop for X`), if one was declared.
pub fn get_type_drop_spec(ty: ty::Ty) -> Option<DefId> {
    match ty.kind() {
        prusti_rustc_interface::middle::ty::TyKind::Adt(adt_def, _) => with_type_spec(|def_spec| {
            def_spec
                .get_type_spec(&adt_def.did())
                .and_then(|type_spec| type_spec.drop_spec)
        }),
        _ => None,
    }
}

pub fn get_type_interior_mut(ty: ty::Ty) -> Vec<DefId> {
    match ty.kind() {
        prusti_rustc_interface::middle::ty::TyKind::Adt(adt_def, _) => with_type_spec(|def_spec| {
            def_spec
                .get_type_spec(&adt_def.did())
                .map(|type_spec| {
                    type_spec
                        .interior_mut
                        .expect_empty_or_inherent()
                        .cloned()
                        .unwrap_or_default()
                })
                .unwrap_or_default()
        }),
        _ => Vec::new(),
    }
}

/// For an `#[interior_mut(EXPR)]`-annotated function (an `as_ptr`-style
/// function in a type's interior-mut list), returns the `DefId` of the
/// `Real`-returning permission-amount function, or `None` for a plain
/// `#[interior_mut]` (always full permission, e.g. `Cell`).
pub fn get_interior_mut_perm(def_id: DefId) -> Option<DefId> {
    let substs = ty::GenericArgs::identity_for_item(vir::with_vcx(|vcx| vcx.tcx()), def_id);
    with_proc_spec(SpecQuery::GetProcKind(def_id, substs), |proc_spec| {
        proc_spec
            .interior_mut_perm
            .extract_with_selective_replacement()
            .copied()
            .flatten()
    })
    .flatten()
}

/// The field path of a `#[field_projection(a.b)]` spec function.
pub fn get_field_projection(def_id: DefId) -> Option<Vec<String>> {
    vir::with_vcx(|vcx| {
        let attrs = prusti_interface::environment::EnvQuery::new(vcx.tcx()).get_attributes(def_id);
        prusti_interface::utils::read_prusti_attr("field_projection", attrs)
            .map(|path| path.split('.').map(str::to_string).collect())
    })
}

/// Whether `def_id` is an `#[interior_mut]`-annotated accessor (with or
/// without a permission expression).
pub fn is_interior_mut_accessor(def_id: DefId) -> bool {
    vir::with_vcx(|vcx| {
        if prusti_interface::environment::EnvQuery::new(vcx.tcx())
            .has_prusti_attribute(def_id, "interior_mut")
        {
            return true;
        }
        // An extern-spec'd accessor (e.g. `Cell::as_ptr`) carries the
        // attribute on its spec item, not on itself: it is an accessor iff
        // its holder type (the referent of its first argument) lists it.
        if !matches!(
            vcx.tcx().def_kind(def_id),
            hir::def::DefKind::Fn | hir::def::DefKind::AssocFn
        ) {
            return false;
        }
        let sig = vcx.tcx().fn_sig(def_id).skip_binder().skip_binder();
        sig.inputs()
            .first()
            .is_some_and(|holder| get_type_interior_mut(holder.peel_refs()).contains(&def_id))
    })
}

/// The `#[pure_unstable]` marking used for the Viper *encoding* of `def_id`:
/// like [`get_pure_unstable`], except that `#[interior_mut]` accessors are
/// `None`. On an accessor the marking only declares the IM *level* of its
/// objects; the accessor's value is map-independent (it identifies a stable
/// address), so it is encoded as a plain pure function. This keeps the IM-QP
/// keys built from accessors stable across differently-phrased maps.
///
/// NOTE: the map argument makes the solver instantiate Viper's built-in
/// `Map_values` axioms on every domain-membership term, whose documented
/// matching loop makes Z3 grind for minutes per assertion. The patched
/// Silicon preamble in `viper/preamble_override` (gating those axioms'
/// triggers on an actual `Map_values` term) is therefore REQUIRED for this
/// encoding to perform.
pub fn get_pure_unstable_encoding(def_id: DefId) -> Option<bool> {
    get_pure_unstable(def_id).filter(|_| !is_interior_mut_accessor(def_id))
}

/// `Some(inner_only)` if `def_id` is a `#[pure_unstable]` function: `inner_only`
/// is `true` for `#[pure_unstable(true)]` (only the level-0 value map is
/// passed) and `false` otherwise (the level-0 and level-1 values are passed).
pub fn get_pure_unstable(def_id: DefId) -> Option<bool> {
    let substs = ty::GenericArgs::identity_for_item(vir::with_vcx(|vcx| vcx.tcx()), def_id);
    with_proc_spec(SpecQuery::GetProcKind(def_id, substs), |proc_spec| {
        proc_spec
            .pure_unstable
            .extract_with_selective_replacement()
            .copied()
            .flatten()
    })
    .flatten()
}

/// A call to a trait method whose statically known impl carries its own
/// specification (an `extern_spec`, or a `#[pure_unstable]` function) goes
/// directly to the impl: such a contract reads the heap (interior-mutable
/// state, pledges of a `&mut` result), so it cannot be stated by the axioms
/// of the trait method's stub.
pub fn resolve_specced_trait_call<'tcx>(
    caller_def_id: DefId,
    def_id: DefId,
    substs: ty::GenericArgsRef<'tcx>,
) -> (DefId, ty::GenericArgsRef<'tcx>) {
    let tcx = vir::with_vcx(|vcx| vcx.tcx());
    if tcx.trait_of_assoc(def_id).is_none() {
        return (def_id, substs);
    }
    let (resolved, resolved_substs) =
        EnvQuery::new(tcx).resolve_method_call(caller_def_id, def_id, substs);
    if resolved == def_id {
        return (def_id, substs);
    }
    let has_extern_spec = with_proc_spec(
        SpecQuery::GetProcKind(resolved, ty::GenericArgs::identity_for_item(tcx, resolved)),
        |proc_spec| proc_spec.extern_spec.is_some(),
    )
    .unwrap_or(false);
    if has_extern_spec || get_pure_unstable_encoding(resolved).is_some() {
        (resolved, resolved_substs)
    } else {
        (def_id, substs)
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
                    let pres = specs.pres.map(|items| vcx.alloc_slice(items));
                    let posts = specs.posts.map(|items| vcx.alloc_slice(items));
                    let pledges = specs.pledges.map(|items| vcx.alloc_slice(items));
                    (specs.extern_spec, pres, posts, pledges)
                },
            )
            .unwrap_or((
                None,
                SpecificationItem::Empty,
                SpecificationItem::Empty,
                SpecificationItem::Empty,
            ));
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

/// The items to encode for one kind of specification, and whether they are
/// expressed in the generics of the item they were inherited from rather than
/// those of the item being encoded.
pub fn spec_items<'vir, T>(spec: &SpecificationItem<&'vir [T]>) -> (&'vir [T], bool) {
    match spec {
        SpecificationItem::Empty => (&[], false),
        SpecificationItem::Inherent(items) => (items, false),
        SpecificationItem::Inherited(items) => (items, true),
        SpecificationItem::Refined(_from, to) => {
            // Here we ignore the original specs: to get to this branch, the
            // task key given to `SpecEnc` was the `DefId` of an trait method
            // implementation, which will happen when encoding the definition
            // of that implementation.
            //
            // At callsites, `MethodCallEnc` will direct the call to the stub
            // method, which uses the `DefId` of the trait item for emitting
            // its specifications.
            (to, false)
        }
    }
}
