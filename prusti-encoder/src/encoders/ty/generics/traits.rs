use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{FunctionIdn, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GParams, GenericParamsEnc, trait_impls::TraitImplEnc},
    pure::TyPureEnc,
};

pub struct TraitEnc;

type TraitArgs = (vir::ManyTyVal, vir::ManyCSnap);
type AssocTypeFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::TyVal>;
type AssocConstFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::Snap>;
type ImplFun<'vir> = FunctionIdn<'vir, TraitArgs, vir::Bool>;
type ImplUnknownFun<'vir> =
    FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap, vir::Int), vir::Bool>;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub funs: TraitFuns<'vir>,
    pub impl_fun: ImplFun<'vir>,
}
impl OutputRefAny for TraitEncOutputRef<'_> {}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
    impl_unknown_fun: vir::Function<'vir>,
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = TraitEncOutput<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for trait_enc in TraitEnc::all_outputs_local_no_errors() {
            // Skip `Sized`, as we need a special encoding for its body. Encoded by `TyConstructorEnc`
            if trait_enc.trait_domain.name == "t_Sized" {
                continue;
            }
            program.add_domain(trait_enc.trait_domain);
            program.add_function(trait_enc.impl_fun);
            program.add_function(trait_enc.impl_unknown_fun);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let params = deps.require_dep::<GenericParamsEnc>(GParams::from(*task_key))?;
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());

            let trait_items = tcx.associated_items(task_key).in_definition_order();
            let assoc_funs = associated_items_funs(vcx, deps, trait_name, trait_items);

            let vpr_funs = assoc_funs.mk_domain_functions(vcx);

            let impl_fun_idn = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                (params.ty_args(), params.const_args()),
                vir::TYPE_BOOL,
            );

            let impl_unknown_fun_idn: ImplUnknownFun = {
                // Omit the `Self` type as it is known to be the "Unknown_type"
                let unknown_args = &params.ty_args()[1..];
                FunctionIdn::new(
                    vir_format_identifier!(vcx, "{trait_name}_unknown_impl"),
                    (unknown_args, params.const_args(), vir::TYPE_INT),
                    vir::TYPE_BOOL,
                )
            };

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    funs: assoc_funs,
                    impl_fun: impl_fun_idn,
                },
            )?;

            let impl_fun_body = {
                let mut trait_impl_checks: Vec<_> = tcx
                    .all_impls(*task_key)
                    .map(|impl_did| {
                        deps.require_dep::<TraitImplEnc>(impl_did)
                            .unwrap()
                            .impl_condition
                    })
                    .collect();

                // Case for unknown types
                let self_expr = params.ty_exprs()[0];

                let is_unknown_type = vcx.mk_adt_discriminator_expr(self_expr, "Unknown_type");

                let unknown_id_destructor =
                    vcx.mk_adt_destructor("non_unit", vir::TYPE_TYVAL, vir::TYPE_INT);
                let extracted_id = unknown_id_destructor.call()(self_expr);

                let unknown_impls = impl_unknown_fun_idn(
                    &params.ty_exprs()[1..],
                    params.const_exprs(),
                    extracted_id,
                );

                let unknown_check = vcx.mk_conj(&[is_unknown_type, unknown_impls]);

                trait_impl_checks.push(unknown_check);

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_unknown_fun = vcx.mk_function(
                impl_unknown_fun_idn,
                (
                    &params.ty_decls()[1..],
                    params.const_decls(),
                    vcx.mk_local_decl("non_unit", vir::TYPE_INT),
                ),
                &[],
                &[],
                None,
                None,
            );

            let impl_fun = vcx.mk_function(
                impl_fun_idn,
                (params.ty_decls(), params.const_decls()),
                &[],
                &[],
                None,
                Some(impl_fun_body),
            );

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "t_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(vpr_funs.as_slice()),
                None,
            );
            Ok((
                TraitEncOutput {
                    trait_domain,
                    impl_fun,
                    impl_unknown_fun,
                },
                (),
            ))
        })
    }
}

#[derive(Debug, Clone)]
pub struct TraitFuns<'a> {
    pub assoc_types: FxHashMap<DefId, AssocTypeFun<'a>>,
    pub assoc_consts: FxHashMap<DefId, AssocConstFun<'a>>,
}

impl<'vir> TraitFuns<'vir> {
    fn mk_domain_functions(&self, vcx: &'vir vir::VirCtxt<'vir>) -> Vec<vir::DomainFunction<'vir>> {
        self.assoc_types
            .values()
            .map(|fun| vcx.mk_domain_function(*fun, false, None))
            .chain(
                self.assoc_consts
                    .values()
                    .map(|fun| vcx.mk_domain_function(*fun, false, None)),
            )
            .collect()
    }
}

/// Collect mappings for associated items of a trait to their corresponding VIR functions.
fn associated_items_funs<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, TraitEnc>,
    trait_name: &str,
    assoc_items: impl Iterator<Item = &'vir ty::AssocItem>,
) -> TraitFuns<'vir> {
    let tcx = vcx.tcx();

    let mut assoc_types = FxHashMap::default();
    let mut assoc_consts = FxHashMap::default();

    let mk_identifier = |item_name, item_type| {
        vir_format_identifier!(vcx, "{trait_name}_assoc_{item_type}_{item_name}")
    };

    for item in assoc_items {
        let assoc_did = item.def_id;
        let name = item.name();
        let params = deps
            .require_dep::<GenericParamsEnc>(GParams::from(assoc_did))
            .unwrap();
        let args = (params.ty_args(), params.const_args());

        match item.kind {
            ty::AssocKind::Type { .. } => {
                let fun = FunctionIdn::new(mk_identifier(name, "type"), args, vir::TYPE_TYVAL);
                assoc_types.insert(assoc_did, fun);
            }
            ty::AssocKind::Const { .. } => {
                let rust_ty = tcx.type_of(assoc_did).skip_binder();
                let decomp = RustTyDecomposition::from_ty(rust_ty, assoc_did);
                let ret_ty = (deps.require_ref::<TyPureEnc>(decomp.ty).unwrap().domain)();

                let fun = FunctionIdn::new(mk_identifier(name, "const"), args, ret_ty);
                assoc_consts.insert(assoc_did, fun);
            }
            ty::AssocKind::Fn { .. } => {
                // unimplemented
            }
        }
    }
    TraitFuns {
        assoc_types,
        assoc_consts,
    }
}
