use pcg::borrow_pcg::FunctionData;
use prusti_interface::specs::is_spec_fn;
use prusti_rustc_interface::{
    data_structures::fx::FxHashSet,
    middle::{mir, ty},
    span::def_id::DefId,
};
use task_encoder::{
    EncodeFullError, EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies,
};
use vir::{CastType, FunctionIdn, HasType, MethodIdn, ViperIdent, vir_format_identifier};

use crate::{
    encoders::{
        MirLocalDefEnc, MirLocalDefEncTask, MirSpecEnc, Pure, TyUseImpureEnc, TyUsePureEnc,
        WandEnc, WandEncTask,
        mir_pure::ExprInput,
        pure::spec::{EncodedPledge, MirSpecEncMode, PledgeExpr},
        ty::{
            RustTyDecomposition,
            generics::{
                GArgCaster, GArgs, GArgsCastEnc, GArgsTyEnc, GParams, GenericParamsEnc,
                r#trait::TraitEnc, trait_impls,
            },
            lifted::TyConstructorEnc,
            use_impure::TyUseImpure,
            use_inhabited::TyUseInhabitedEnc,
            use_pure::TyUsePure,
        },
    },
    trait_support::is_function_with_body,
};

pub struct TraitFnEnc;

#[derive(Debug, Clone, Copy)]
pub struct TraitFnEncOutputRef<'vir> {
    pub pre_func: FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    /// Takes the result, then the arguments before the call, then the
    /// arguments after it (see `LaterSnap`).
    pub post_func:
        FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    /// The pledges of a call through the trait: takes the result just before
    /// its borrow expires, then the arguments before the call, then the
    /// arguments after the expiry (see `trait_pledge`).
    pub pledge_func:
        FunctionIdn<'vir, (vir::Snap, vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    pub call_stub_impure: Option<MethodIdn<'vir, (vir::ManyRef, vir::ManyTyVal, vir::ManyCSnap)>>,
    pub call_stub_pure_caller:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    pub call_stub_pure_function:
        Option<FunctionIdn<'vir, (vir::ManySnap, vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
}

impl<'vir> OutputRefAny for TraitFnEncOutputRef<'vir> {}

impl TaskEncoder for TraitFnEnc {
    task_encoder::encoder_cache!(TraitFnEnc);
    const ENCODER_NAME: &'static str = "trait fn encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitFnEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = (
        vir::Domain<'vir>,
        Vec<vir::Function<'vir>>,
        Vec<vir::Method<'vir>>,
    );

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for (dom, funcs, methods) in Self::all_outputs_local_no_errors(program) {
            program.add_domain(dom);
            for func in funcs {
                program.add_function(func);
            }
            for method in methods {
                program.add_method(method);
            }
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();

            let assoc_item = tcx
                .opt_associated_item(*task_key)
                .expect("task key should be the associated item of a trait");
            let def_id = assoc_item.def_id;
            let span = vcx.tcx().def_span(def_id);
            assert!(matches!(assoc_item.kind, ty::AssocKind::Fn { .. }));
            assert_eq!(def_id, *task_key);

            // Prusti specifications on trait methods emit additional spec-
            // only fn items (with default implementations). These should never
            // be passed here, even though they are part of the trait as far as
            // Rust typing is concerned.
            assert!(!is_spec_fn(tcx, def_id));

            let trait_def_id = assoc_item
                .trait_container(tcx)
                .expect("task key should be the associated item of a trait");

            let trait_name = ViperIdent::from_def_id(vcx, trait_def_id);

            let mut axioms = Vec::new();
            let mut funcs = Vec::new();
            let mut dom_funcs = Vec::new();
            let mut methods = Vec::new();

            // item_generics also includes parameters of trait itself
            let item_params = GParams::from(def_id);
            let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
            let item_name = ViperIdent::from_def_id(vcx, def_id);

            let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
                def_id,
                all_locals: false,
            })?;
            let arg_count = local_defs.arg_count + 1;
            let arg_types = vcx.alloc_slice(&local_defs.snap_ty_args().collect::<Vec<_>>());
            let two_state_arg_types = vcx.alloc_slice(&[arg_types, arg_types].concat());
            let return_type = local_defs.snap_ty_return();
            let ref_args = vcx.alloc_slice(&vec![vir::TYPE_REF; arg_count]);

            let is_pure = crate::encoders::is_function_pure(
                def_id,
                GArgs::new(item_params, item_params.rust_params()),
            );

            let pre_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_pre_{item_name}"),
                (
                    arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            let post_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_post_{item_name}"),
                (
                    return_type,
                    two_state_arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );
            let pledge_func = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_fn_pledge_{item_name}"),
                (
                    return_type,
                    two_state_arg_types,
                    item_generics.ty_args(),
                    item_generics.const_args(),
                ),
                vir::TYPE_BOOL,
            );

            let call_stub_impure = (!is_pure).then(|| {
                MethodIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        ref_args,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                )
            });
            let call_stub_pure_caller = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_cfn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            let call_stub_pure_function = is_pure.then(|| {
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_fn_stub_{item_name}"),
                    (
                        arg_types,
                        item_generics.ty_args(),
                        item_generics.const_args(),
                    ),
                    return_type,
                )
            });
            deps.emit_output_ref(
                *task_key,
                TraitFnEncOutputRef {
                    pre_func,
                    post_func,
                    pledge_func,
                    call_stub_impure,
                    call_stub_pure_caller,
                    call_stub_pure_function,
                },
            )?;
            // The stubs' semantics are given by the impls' axioms; require the
            // trait so that its impls' condition/axiom triggers are registered
            // (foreign traits are not encoded by `encode_all_in_crate`).
            deps.require_ref::<TraitEnc>(trait_def_id)?;
            dom_funcs.push(vcx.mk_domain_function(pre_func, false, None));
            dom_funcs.push(vcx.mk_domain_function(post_func, false, None));
            dom_funcs.push(vcx.mk_domain_function(pledge_func, false, None));

            // The stub emitted below is only useful together with the axioms
            // bridging the abstract pre/post functions to concrete impl
            // specs. Unlock, per impl of the trait, the axioms of just the
            // item implementing this function once the impl's constructor
            // keys are requested - the same gating as the impl's condition
            // (see `TraitEnc`), but calling a trait function must not pull in
            // the trait's whole machinery. An impl that inherits a pure
            // default body instead unlocks the axiom stating that body at its
            // trait refs. Only final definitions are assumed (see
            // `final_leaf_def`).
            let has_body = is_function_with_body(vcx.tcx(), def_id);
            for impl_did in trait_impls::implementing_impls(tcx, trait_def_id) {
                let Some(leaf) = trait_impls::final_leaf_def(tcx, impl_did, def_id) else {
                    continue;
                };
                let keys = trait_impls::impl_unlock_keys(impl_did);
                let impl_span = tcx.def_span(impl_did);
                if !leaf.defining_node.is_from_trait() {
                    let item_did = leaf.item.def_id;
                    TyConstructorEnc::on_all_requested(keys, move || {
                        let _ = trait_impls::TraitImplItemEnc::encode(
                            (impl_did, item_did),
                            false,
                            impl_span,
                        );
                    });
                } else if has_body && is_pure {
                    TyConstructorEnc::on_all_requested(keys, move || {
                        let _ = trait_impls::TraitImplDefaultFnEnc::encode(
                            (impl_did, def_id),
                            false,
                            impl_span,
                        );
                    });
                }
            }

            let func_args = local_defs.local_decl_args().collect::<Vec<_>>();
            let func_arg_exprs = vcx.alloc_slice(
                &func_args
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
            );
            let func_ret = local_defs.local_decl_ret();

            let spec = deps.require_dep_spanned::<MirSpecEnc>(
                (def_id, def_id, MirSpecEncMode::PureWithoutResult),
                span,
            )?;
            let pres = vcx.mk_conj(&spec.pre_exprs().collect::<Vec<_>>());
            let pre_func_call = pre_func.call()(
                func_arg_exprs,
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_pre_{item_name}_base",
                ),
                vir::expr! {
                    forall ..[func_args], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[pre_func_call]}
                        (pres) ==> (pre_func_call)
                },
            ));
            // A default body is not part of the trait's contract: impls may
            // override it with a different result.
            let posts = vcx.mk_conj(&spec.post_exprs().collect::<Vec<_>>());
            let func_args_later = local_defs.local_decl_args_later();
            let two_state_arg_exprs = vcx.alloc_slice(
                &func_args
                    .iter()
                    .chain(&func_args_later)
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
            );
            let post_func_call = post_func.call()(
                vcx.mk_local_ex(func_ret),
                two_state_arg_exprs,
                item_generics.ty_exprs(),
                item_generics.const_exprs(),
            );
            // Impls may weaken the preconditions, so a call can be valid
            // outside them; the trait's postconditions are only promised
            // where they held.
            axioms.push(vcx.mk_domain_axiom(
                vir_format_identifier!(
                    vcx,
                    "{trait_name}_fn_post_{item_name}_base",
                ),
                vir::expr! {
                    forall [func_ret], ..[func_args], ..[func_args_later], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[post_func_call]}
                        (post_func_call) ==> ((pres) ==> (posts))
                },
            ));

            // The trait's own pledges, for a call through the trait (see
            // `trait_pledge`). Every impl satisfies them: it inherits them (an
            // impl cannot declare pledges of its own for a trait method), or
            // the default body, which is verified against them. One with an
            // expiry obligation is left out: a call through the trait does
            // not establish the obligation.
            let pledge_args = PledgeExpr::two_state_args(
                vcx.mk_local_ex(func_ret),
                func_arg_exprs,
                &func_args_later
                    .iter()
                    .map(|arg| vcx.mk_local_ex(arg))
                    .collect::<Vec<_>>(),
            );
            let pledges = spec
                .pledges
                .iter()
                .filter(|pledge| pledge.expiry_obligation.is_none())
                .map(|pledge| pledge.expiry_postcondition.expr(pledge_args))
                .collect::<Vec<_>>();
            if !pledges.is_empty() {
                let pledges = vcx.mk_conj(&pledges);
                let pledge_func_call = pledge_func.call()(
                    vcx.mk_local_ex(func_ret),
                    two_state_arg_exprs,
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                );
                axioms.push(vcx.mk_domain_axiom(
                    vir_format_identifier!(vcx, "{trait_name}_fn_pledge_{item_name}_base"),
                    vir::expr! {
                        forall [func_ret], ..[func_args], ..[func_args_later], ..[item_generics.ty_decls()], ..[item_generics.const_decls()] :: {[pledge_func_call]}
                            (pledge_func_call) ==> ((pres) ==> (pledges))
                    },
                ));
            }

            if is_pure {
                let mut stub_pres = Vec::new();
                let mut stub_posts = Vec::new();
                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| vcx.mk_local_ex(arg.local_snap))
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                // A pure function cannot change its arguments.
                let args = local_defs
                    .args()
                    .map(|arg| vcx.mk_local_ex(arg.local_snap))
                    .collect::<Vec<_>>();
                stub_posts.push(post_func.call()(
                    vcx.mk_result(local_defs.snap_ty_return()),
                    vcx.alloc_slice(&[args.as_slice(), &args].concat()),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));

                // If the call succeeds, then its return type is definitely inhabited
                // We need this postcondition to generate impure wrapper fns
                // See tests/verify/pass/extern-spec/module-arg.rs
                let ret_ty = tcx
                    .instantiate_and_normalize_erasing_regions(
                        ty::GenericArgs::identity_for_item(tcx, def_id),
                        ty::TypingEnv::post_analysis(tcx, def_id),
                        tcx.fn_sig(def_id),
                    )
                    .skip_binder()
                    .output();
                let ret_ty = RustTyDecomposition::from_ty(ret_ty, def_id);
                stub_posts.push(deps.require_ref::<TyUseInhabitedEnc>(ret_ty)?.inhabited());
                // stub_posts.push(local_defs.ret().inhabited);

                let wrapped_call = call_stub_pure_function.unwrap().call()(
                    func_arg_exprs,
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                );
                funcs.push(vcx.mk_function(
                    call_stub_pure_caller.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    Some(&vir::DecreasesGenData::Star),
                    Some(wrapped_call),
                ));
                funcs.push(vcx.mk_function(
                    call_stub_pure_function.unwrap(),
                    (
                        &func_args,
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_posts),
                    None,
                    None,
                ));
            } else {
                let mut stub_pres = Vec::new();
                let mut stub_posts = Vec::new();
                let mut args = Vec::with_capacity(arg_count + item_params.count());
                for arg_idx in (0..arg_count).map(mir::Local::from) {
                    let name_p = local_defs[arg_idx].local.name;
                    args.push(vir::vir_local_decl! { vcx; [name_p] : Ref });
                    if arg_idx != mir::RETURN_PLACE {
                        stub_pres.push(local_defs[arg_idx].impure_pred);
                    }
                }
                stub_posts.push(local_defs[mir::RETURN_PLACE].impure_pred);
                // Like a regular method, the stub takes (and returns) what the
                // arguments and the result point to, and the wands that give
                // back what the result borrows. The deep snapshots passed to
                // the pre- and postcondition functions below read it.
                let wands = deps.require_dep::<WandEnc>(WandEncTask {
                    data: FunctionData::new(def_id),
                })?;
                stub_pres.extend(wands.indirect_pres(vcx, &local_defs, deps));
                stub_posts.extend(wands.indirect_posts(vcx, &local_defs, deps));
                stub_posts.extend(wands.wand_posts(vcx, &local_defs, true, deps));

                stub_pres.push(pre_func.call()(
                    vcx.alloc_slice(
                        &local_defs
                            .args()
                            .map(|arg| arg.impure_snap)
                            .collect::<Vec<_>>(),
                    ),
                    item_generics.ty_exprs(),
                    item_generics.const_exprs(),
                ));
                // The arguments after the call: what the result borrows is only
                // given back once the borrow expires.
                let sig = tcx.fn_sig(def_id).instantiate_identity().skip_binder();
                let blocked = wands.blocked_args();
                let pre_args = local_defs
                    .args()
                    .map(|arg| vcx.mk_old_expr(arg.impure_snap))
                    .collect::<Vec<_>>();
                let mut later_args = Vec::with_capacity(pre_args.len());
                for (idx, (pre, decl)) in pre_args.iter().zip(&func_args_later).enumerate() {
                    let held = !blocked.contains(&mir::Local::from_usize(idx + 1));
                    let later = LaterSnap::new(deps, sig.inputs()[idx], def_id, held, false)?;
                    later_args.push((later.snap(*pre), *decl));
                }
                stub_posts.push(with_unknowns(vcx, &later_args, |later_args| {
                    post_func.call()(
                        local_defs.ret().impure_snap,
                        vcx.alloc_slice(&[pre_args.as_slice(), later_args].concat()),
                        item_generics.ty_exprs(),
                        item_generics.const_exprs(),
                    )
                }));

                methods.push(vcx.mk_method(
                    call_stub_impure.unwrap(),
                    (
                        args.as_slice(),
                        item_generics.ty_decls(),
                        item_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&stub_pres),
                    vcx.alloc_slice(&stub_posts),
                    None,
                ));
            }

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_fns_{trait_name}_{item_name}"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok(((trait_domain, funcs, methods), ()))
        })
    }
}

/// How the value of an argument (or the result) of a trait function in a
/// later state (after the call, or when a borrow of the result expires) is
/// obtained from its snapshot in an earlier state, for the specifications
/// over two states in the trait's axioms.
#[derive(Clone, Copy)]
pub(crate) enum LaterSnap<'vir> {
    /// The type holds no value behind a mutable reference (it constructs no
    /// deep snapshot), so the snapshot does not change.
    Unchanged,
    /// A mutable reference whose referent is held then: its address and
    /// pointer metadata, with the referent's value then (with `at_lhs`, in
    /// the state of the left-hand side of the enclosing wand, i.e. just
    /// before the borrow expires).
    Rebuilt {
        ref_ty: TyUsePure<'vir>,
        referent_caster: GArgCaster<'vir, Pure>,
        referent_ty: TyUseImpure<'vir>,
        at_lhs: bool,
    },
    /// Unknown: the referent is not held then (e.g. it is borrowed by the
    /// result), or the mutable references are inside another type (e.g. a
    /// struct), whose deep snapshot is not rebuilt.
    Unknown,
}

impl<'vir> LaterSnap<'vir> {
    /// For a value of type `ty` (in the context of `def_id`), whose referents
    /// are `held` in the later state.
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut TaskEncoderDependencies<'vir, E>,
        ty: ty::Ty<'vir>,
        def_id: DefId,
        held: bool,
        at_lhs: bool,
    ) -> Result<Self, EncodeFullError<'vir, E>> {
        let decomp = RustTyDecomposition::from_ty(ty, def_id);
        if !decomp.ty.construct_deep_snapshot {
            return Ok(Self::Unchanged);
        }
        if !held || !matches!(ty.kind(), ty::TyKind::Ref(.., ty::Mutability::Mut)) {
            return Ok(Self::Unknown);
        }
        let inner = decomp.ty.expect_mutref();
        let normalized = inner
            .referent
            .decompose_compare_normalize(decomp.ty.params, decomp.args);
        let referent = inner
            .referent
            .decompose_context(decomp.ty.params, decomp.args);
        Ok(Self::Rebuilt {
            ref_ty: deps.require_dep::<TyUsePureEnc>(decomp)?,
            referent_caster: deps.require_dep::<GArgsCastEnc<Pure>>(normalized)?,
            referent_ty: deps.require_dep::<TyUseImpureEnc>(referent)?,
            at_lhs,
        })
    }

    /// The value in the later state, given the snapshot `earlier`; `None` if
    /// it is unknown.
    pub(crate) fn snap<Curr, Next>(
        &self,
        earlier: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> Option<vir::ExprGenSnap<'vir, Curr, Next>> {
        match *self {
            Self::Unchanged => Some(earlier),
            Self::Rebuilt {
                ref_ty,
                referent_caster,
                referent_ty,
                at_lhs,
            } => vir::with_vcx(|vcx| {
                let ref_ty = ref_ty.expect_mutref();
                let earlier = earlier.downcast_ty();
                let addr = ref_ty.deref_access(earlier);
                let metadata = ref_ty.metadata_access(earlier);
                let mut value = referent_ty.ref_to_deep_snap(addr);
                if at_lhs {
                    value = vcx.mk_old_lhs_expr(value);
                }
                let value = referent_caster.cast_to_caller_ctx(value);
                Some(ref_ty.prim_to_snap(addr, metadata, value).upcast_ty())
            }),
            Self::Unknown => None,
        }
    }
}

/// `f(values)`, where each unknown value (`None`) is a fresh, unconstrained
/// one: a variable, named after the given declaration, bound by an
/// existential quantifier. Nothing is known about it, so a specification
/// constraining it cannot contradict anything.
pub(crate) fn with_unknowns<'vir, Curr: 'vir, Next: 'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    values: &[(
        Option<vir::ExprGenSnap<'vir, Curr, Next>>,
        vir::LocalDeclSnap<'vir>,
    )],
    f: impl FnOnce(&[vir::ExprGenSnap<'vir, Curr, Next>]) -> vir::ExprGenBool<'vir, Curr, Next>,
) -> vir::ExprGenBool<'vir, Curr, Next> {
    let mut unknowns = Vec::new();
    let values = values
        .iter()
        .map(|(value, decl)| {
            value.unwrap_or_else(|| {
                let name = vir::vir_format!(vcx, "{}_unknown", decl.name);
                let unknown = vcx.mk_local_decl(name, decl.ty());
                unknowns.push(unknown);
                vcx.mk_local_ex(unknown)
            })
        })
        .collect::<Vec<_>>();
    vcx.mk_exists_expr(vcx.alloc_slice(&unknowns), &[], f(&values))
}

/// The pledge of a call through the trait function `def_id`, for its wand
/// that gives back the arguments `given_back`: `fn_pledge(result, args,
/// args_later)`, with the result just before its borrow expires and the
/// arguments after that (see `LaterSnap`). The impls' axioms define
/// `fn_pledge` (see `TraitImplItemEnc`).
///
/// Only the result and the arguments are read when reifying (as for
/// `PledgeExpr::pledge_args`), so that at a call site the callee's generics
/// in the rest of the expression are substituted.
pub(crate) fn trait_pledge<'vir, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, E>,
    def_id: DefId,
    given_back: &FxHashSet<mir::Local>,
) -> Result<EncodedPledge<'vir>, EncodeFullError<'vir, E>> {
    let pledge_func = deps.require_ref::<TraitFnEnc>(def_id)?.pledge_func;
    let params = GParams::from(def_id);
    let generics = deps.require_dep::<GArgsTyEnc>(GArgs::new(params, params.rust_params()))?;
    let local_defs = deps.require_dep::<MirLocalDefEnc>(MirLocalDefEncTask::Local {
        def_id,
        all_locals: false,
    })?;
    let sig = vcx
        .tcx()
        .fn_sig(def_id)
        .instantiate_identity()
        .skip_binder();
    let read = |local: mir::Local, ty: vir::TypeSnap<'vir>| {
        vcx.mk_lazy_expr(
            "trait_pledge_arg",
            ty,
            Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[&local].kind),
        )
    };
    let pre = local_defs
        .args()
        .enumerate()
        .map(|(idx, arg)| read(mir::Local::from_usize(idx + 1), arg.local_snap.ty()))
        .collect::<Vec<_>>();
    let result = read(
        mir::Local::from_usize(pre.len() + 1),
        local_defs.snap_ty_return(),
    );
    let mut values = vec![(
        LaterSnap::new(deps, sig.output(), def_id, true, true)?.snap(result),
        local_defs.local_decl_ret(),
    )];
    for (idx, (pre, decl)) in pre
        .iter()
        .zip(local_defs.local_decl_args_later())
        .enumerate()
    {
        let held = given_back.contains(&mir::Local::from_usize(idx + 1));
        let later = LaterSnap::new(deps, sig.inputs()[idx], def_id, held, false)?;
        values.push((later.snap(*pre), decl));
    }
    let expr = with_unknowns(vcx, &values, |values| {
        pledge_func.call()(
            values[0],
            vcx.alloc_slice(&[pre.as_slice(), &values[1..]].concat()),
            generics.get_ty(),
            generics.get_const(),
        )
    });
    Ok(EncodedPledge {
        expiry_obligation: None,
        expiry_postcondition: PledgeExpr::new(def_id, expr),
    })
}
