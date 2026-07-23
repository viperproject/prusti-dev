use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, vir_format_identifier};

use crate::encoders::{
    TyUsePureEnc,
    ty::{
        RustTy, RustTyDecomposition,
        generics::{
            GParams, GenericParams, GenericParamsEnc,
            trait_impls::{self, TraitImplConditionEnc},
        },
        lifted::TyConstructorEnc,
    },
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub assoc_types:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
    pub assoc_consts:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_did: DefId,
    trait_domain: vir::Domain<'vir>,
    impl_fun_idn: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
    trait_generics: GenericParams<'vir>,
    unknown_type_check: vir::ExprBool<'vir>,
}

impl<'vir> OutputRefAny for TraitEncOutputRef<'vir> {}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);
    const ENCODER_NAME: &'static str = "trait encoder";

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = TraitEncOutput<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        // Which impls contribute to a trait's `impl_fun` is only known once
        // all encoding is done (the impls of constructed types, see
        // `register_impl_triggers`), so the function is assembled here,
        // analogously to how `TyConstructorEnc` assembles the `Type` ADT.
        let mut conditions: FxHashMap<DefId, Vec<vir::ExprBool<'vir>>> = FxHashMap::default();
        for (trait_did, condition, axioms) in
            trait_impls::TraitImplConditionEnc::all_outputs_local_no_errors(program)
        {
            conditions.entry(trait_did).or_default().push(condition);
            program.add_domain(axioms);
        }
        vir::with_vcx(|vcx| {
            for output in TraitEnc::all_outputs_local_no_errors(program) {
                program.add_domain(output.trait_domain);
                let mut checks = conditions.remove(&output.trait_did).unwrap_or_default();
                checks.push(output.unknown_type_check);
                // TODO: putting the body in the postcondition will result in a
                // matching loop for recursive definitions. We can avoid this by
                // manually axiomatising the function, or by adding adt-based
                // unfolding to Viper.
                let ensures = vcx.mk_eq_expr(vcx.mk_result(vir::TYPE_BOOL), vcx.mk_disj(&checks));
                let impl_fun = vcx.mk_function(
                    output.impl_fun_idn,
                    (
                        output.trait_generics.ty_decls(),
                        output.trait_generics.const_decls(),
                    ),
                    &[],
                    vcx.alloc_slice(&[ensures]),
                    Some(&vir::DecreasesGenData::Star),
                    None,
                );
                program.add_function(impl_fun);
            }
        })
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let trait_params = Self::trait_params(*task_key);
            let trait_generics = deps.require_dep::<GenericParamsEnc>(trait_params)?;

            let trait_args = (trait_generics.ty_args(), trait_generics.const_args());

            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());

            let mut dom_funcs = Vec::new();
            let mut assoc_types = FxHashMap::default();
            let mut assoc_consts = FxHashMap::default();

            for item in tcx.associated_items(task_key).in_definition_order() {
                let item_did = item.def_id;

                // item_generics also includes parameters of trait itself
                let item_params = GParams::from(item_did);
                let item_generics = deps.require_dep::<GenericParamsEnc>(item_params)?;
                let item_name = tcx.item_name(item_did);

                let args = (item_generics.ty_args(), item_generics.const_args());
                match item.kind {
                    ty::AssocKind::Type { .. } => {
                        let idn =
                            vir_format_identifier!(vcx, "{trait_name}_assoc_type_{item_name}");
                        let fun = FunctionIdn::new(idn, args, vir::TYPE_TYVAL);
                        assoc_types.insert(item_did, fun);
                        dom_funcs.push(vcx.mk_domain_function(fun, false, None));
                    }
                    ty::AssocKind::Const { .. } => {
                        let rust_ty = tcx.type_of(item_did).skip_binder();
                        let ty = RustTyDecomposition::from_ty(rust_ty, item_did);
                        let ret_ty = deps.require_ref::<TyUsePureEnc>(ty).unwrap().snapshot;

                        let idn =
                            vir_format_identifier!(vcx, "{trait_name}_assoc_const_{item_name}");
                        let fun = FunctionIdn::new(idn, args, ret_ty);
                        assoc_consts.insert(item_did, fun);
                        dom_funcs.push(vcx.mk_domain_function(fun, false, None));
                    }
                    ty::AssocKind::Fn { .. } => {}
                }
            }

            let impl_fun = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                trait_args,
                vir::TYPE_BOOL,
            );
            // Omit the `Self` type as it is known to be the unknown type
            let impl_for_unknown_fun =
                FunctionIdn::<(vir::Int, vir::ManyTyVal, vir::ManyCSnap), _>::new(
                    vir_format_identifier!(vcx, "{trait_name}_impl_for_unknown"),
                    (vir::TYPE_INT, &trait_args.0[1..], trait_args.1),
                    vir::TYPE_BOOL,
                );

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    assoc_types,
                    assoc_consts,
                    impl_fun,
                },
            )?;

            // The `impl_fun` body (a disjunction over the conditions of this
            // trait's impls) is assembled in `emit_outputs`, once it is known
            // which impls are relevant.
            for impl_did in tcx.all_impls(*task_key) {
                // An `impl<T> MyTrait<ArgType> for MyType<T, OtherType>` is
                // only relevant if a) it is in the current crate (in which
                // case it will be encoded by `TraitImplEnc`) or b) the
                // `TyConstructorEnc` has been called with `MyType`,
                // `OtherType` and `ArgType` (we guard on the conjunction of
                // these below). Gating on the trait args (not just the self
                // type) is fail-closed: any site that states a dependence on
                // this impl does so by applying `impl_fun` to type
                // expressions for the full trait ref, and building those
                // requests exactly the constructors gated on here. Without
                // the arg gate, encoding one impl's condition constructs its
                // arg types as a side effect, unlocking further impls
                // transitively (e.g. `Array` alone would pull in every
                // `core::arch` <-> `Simd` `From` impl).
                let impl_trait_ref = tcx.impl_trait_ref(impl_did).unwrap().instantiate_identity();
                let mut keys = Vec::new();
                fn collect_ctor_keys<'vir>(
                    ty: ty::Ty<'vir>,
                    ctx: DefId,
                    out: &mut Vec<RustTy<'vir>>,
                ) {
                    let decomp = RustTyDecomposition::from_ty(ty, ctx);
                    if decomp.ty.specifics.is_param() {
                        return;
                    }
                    out.push(decomp.ty);
                    for inner in decomp.args.args().iter().filter_map(|arg| arg.as_type()) {
                        collect_ctor_keys(inner, ctx, out);
                    }
                }
                for ty in impl_trait_ref.args.iter().filter_map(|arg| arg.as_type()) {
                    collect_ctor_keys(ty, impl_did, &mut keys);
                }
                let span = tcx.def_span(impl_did);
                TyConstructorEnc::on_all_requested(keys, move || {
                    let _ = TraitImplConditionEnc::encode(impl_did, false, span);
                });
            }
            let unknown_type_check = {
                let self_expr = trait_generics.ty_exprs()[0];

                let is_unknown_type =
                    vcx.mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);

                let extracted_id =
                    TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                let unknown_impls = impl_for_unknown_fun(
                    extracted_id,
                    &trait_generics.ty_exprs()[1..],
                    trait_generics.const_exprs(),
                );

                vir::expr! { vcx;
                     (is_unknown_type) && (unknown_impls)
                }
            };

            let impl_for_unknown_fun = vcx.mk_domain_function(impl_for_unknown_fun, false, None);
            dom_funcs.push(impl_for_unknown_fun);

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "trait_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(&dom_funcs),
                None,
            );

            Ok((
                TraitEncOutput {
                    trait_did: *task_key,
                    trait_domain,
                    impl_fun_idn: impl_fun,
                    trait_generics,
                    unknown_type_check,
                },
                (),
            ))
        })
    }
}

impl TraitEnc {
    pub(super) fn trait_params<'tcx>(trait_did: DefId) -> GParams<'tcx> {
        GParams::from(trait_did).with_suffix("trait")
    }
}
