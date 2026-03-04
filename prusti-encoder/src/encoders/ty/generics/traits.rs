use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder, TaskEncoderDependencies};
use vir::{Arity, FunctionIdn, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GParams, GenericParamsEnc, trait_impls::TraitImplEnc},
    lifted::TyConstructorEnc,
    pure::TyPureEnc,
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitEncOutputRef<'vir> {
    pub trait_name: &'vir str,
    pub fns: TraitFuns<'vir>,
    pub impl_fun: FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool>,
}
impl OutputRefAny for TraitEncOutputRef<'_> {}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputRef<'vir> = TraitEncOutputRef<'vir>;
    type OutputFullLocal<'vir> = Option<TraitEncOutput<'vir>>;

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let params = deps
                .require_dep::<GenericParamsEnc>(GParams::from(*task_key).with_suffix("trait"))?;
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());

            let trait_items = tcx.associated_items(task_key).in_definition_order();
            let assoc_fns = Self::associated_items_fns(vcx, deps, trait_name, trait_items);

            let mut funcs = assoc_fns.mk_domain_functions(vcx);

            let args = (params.ty_args(), params.const_args());
            let decls = (params.ty_decls(), params.const_decls());
            let impl_fun_idn = Self::trait_impl_idn(vcx, trait_name, args);
            let unkown_impl_fun_idn = Self::trait_unknown_impl_idn(vcx, trait_name, args);

            // Emit the impl function reference early, so that it can be used to encode caller
            // bounds without causing dependency cycles.
            deps.emit_output_ref(
                *task_key,
                TraitEncOutputRef {
                    trait_name,
                    fns: assoc_fns,
                    impl_fun: impl_fun_idn,
                },
            )?;

            // When encoding `Sized`, emitting of the impl function is handled by `SizedTraitEnc`
            if tcx.lang_items().sized_trait() == Some(*task_key) {
                return Ok((None, ()));
            }

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
                {
                    let self_expr = params.ty_exprs()[0];

                    let is_unknown_type = vcx
                        .mk_adt_discriminator_expr(self_expr, TyConstructorEnc::UNKNOWN_TYPE_NAME);

                    let extracted_id =
                        TyConstructorEnc::unknown_type_id_accessor(vcx).call()(self_expr);

                    let unknown_impls = unkown_impl_fun_idn(
                        extracted_id,
                        &params.ty_exprs()[1..],
                        params.const_exprs(),
                    );

                    let unknown_check = vir::expr! { vcx;
                         (is_unknown_type) && (unknown_impls)
                    };

                    trait_impl_checks.push(unknown_check);
                }

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_fun =
                vcx.mk_function(impl_fun_idn, decls, &[], &[], None, Some(impl_fun_body));

            let impl_unknown_fun = vcx.mk_domain_function(unkown_impl_fun_idn, false, None);
            funcs.push(impl_unknown_fun);

            let trait_domain = vcx.mk_domain(
                Self::trait_domain_idn(vcx, trait_name),
                &[],
                &[],
                vcx.alloc_slice(funcs.as_slice()),
                None,
            );
            Ok((
                Some(TraitEncOutput {
                    trait_domain,
                    impl_fun,
                }),
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in TraitEnc::all_outputs_local_no_errors() {
            let Some(output) = output else { continue };
            program.add_domain(output.trait_domain);
            program.add_function(output.impl_fun);
        }
    }
}

#[derive(Debug, Clone)]
pub struct TraitFuns<'vir> {
    pub assoc_types:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>>,
    pub assoc_consts:
        FxHashMap<DefId, FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Snap>>,
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

impl TraitEnc {
    /// Collect mappings for associated items of a trait to their corresponding VIR functions.
    fn associated_items_fns<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
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

    pub(super) fn trait_impl_idn<'vir, 'a>(
        vcx: &'vir vir::VirCtxt<'vir>,
        trait_name: &'a str,
        args: <(vir::ManyTyVal, vir::ManyCSnap) as Arity>::Tys<'vir>,
    ) -> FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::Bool> {
        FunctionIdn::new(
            vir_format_identifier!(vcx, "{trait_name}_impl"),
            args,
            vir::TYPE_BOOL,
        )
    }

    pub(super) fn trait_unknown_impl_idn<'vir, 'a>(
        vcx: &'vir vir::VirCtxt<'vir>,
        trait_name: &'a str,
        args: <(vir::ManyTyVal, vir::ManyCSnap) as Arity>::Tys<'vir>,
    ) -> FunctionIdn<'vir, (vir::Int, vir::ManyTyVal, vir::ManyCSnap), vir::Bool> {
        // Omit the `Self` type as it is known to be the unknown type
        let ty_args = &args.0[1..];
        let const_args = args.1;
        FunctionIdn::new(
            vir_format_identifier!(vcx, "{trait_name}_unknown_impl"),
            (vir::TYPE_INT, ty_args, const_args),
            vir::TYPE_BOOL,
        )
    }

    pub(super) fn trait_domain_idn<'vir, 'a>(
        vcx: &'vir vir::VirCtxt<'vir>,
        trait_name: &'a str,
    ) -> vir::ViperIdent<'vir> {
        vir_format_identifier!(vcx, "t_{trait_name}")
    }
}
