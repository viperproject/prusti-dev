use prusti_rustc_interface::{middle::ty::AssocKind, span::def_id::DefId};
use rustc_hash::FxHashMap;
use task_encoder::{EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{AdtDestructorWrapper, CallableIdn, FunctionIdn, vir_format_identifier};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::{GParams, GenericParamsEnc},
    lifted::TyConstructorEnc,
};

pub struct TraitEnc;

#[derive(Debug, Clone)]
pub struct TraitData<'vir> {
    pub trait_name: &'vir str,
    pub type_did_fun_mapping: FxHashMap<DefId, FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>>,
    pub impl_fun: FunctionIdn<'vir, vir::ManyTyVal, vir::Bool>,
}

#[derive(Debug, Clone)]
pub struct TraitEncOutput<'vir> {
    trait_domain: vir::Domain<'vir>,
    impl_fun: vir::Function<'vir>,
    impl_fun_unknown: vir::Function<'vir>,
}

impl TaskEncoder for TraitEnc {
    task_encoder::encoder_cache!(TraitEnc);

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    type TaskDescription<'vir> = DefId;

    type OutputFullDependency<'vir> = TraitData<'vir>;
    type OutputFullLocal<'vir> = TraitEncOutput<'vir>;

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for trait_enc in TraitEnc::all_outputs_local_no_errors() {
            program.add_domain(trait_enc.trait_domain);
            program.add_function(trait_enc.impl_fun);
            program.add_function(trait_enc.impl_fun_unknown);
        }
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let params = deps.require_dep::<GenericParamsEnc>(GParams::from(*task_key))?;
            let trait_name = vcx.alloc_str(tcx.item_name(task_key).as_str());
            let type_did_fun_mapping = tcx
                .associated_items(task_key)
                .in_definition_order()
                .filter(|item| matches!(item.kind, AssocKind::Type { data: _ }))
                .map(|item| {
                    let params_type = deps
                        .require_dep::<GenericParamsEnc>(GParams::from(item.def_id))
                        .unwrap();
                    (
                        item.def_id,
                        FunctionIdn::new(
                            vir_format_identifier!(
                                vcx,
                                "{trait_name}_Assoc_{}_func",
                                tcx.item_name(item.def_id),
                            ),
                            vcx.alloc_slice(&vec![vir::TYPE_TYVAL; params_type.ty_exprs().len()]), // params_type also includes parameters of trait itself
                            vir::TYPE_TYVAL,
                        ),
                    )
                })
                .collect::<FxHashMap<_, _>>();
            let funcs = type_did_fun_mapping
                .values()
                .map(|function_idn| vcx.mk_domain_function(*function_idn, false, None))
                .collect::<Vec<_>>();

            let impl_fun_idn = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl"),
                vcx.alloc_slice(&(vec![vir::TYPE_TYVAL; params.ty_exprs().len()])),
                vir::TYPE_BOOL,
            );

            let impl_fun_unknown_idn: FunctionIdn<'vir, vir::Int, vir::Bool> = FunctionIdn::new(
                vir_format_identifier!(vcx, "{trait_name}_impl_unknown"),
                vir::TYPE_INT,
                vir::TYPE_BOOL,
            );

            let impl_fun_unknown = vcx.mk_function(
                impl_fun_unknown_idn,
                (vcx.mk_local_decl("non_unit", vir::TYPE_INT),),
                &[],
                &[],
                None,
                None,
            );

            let impl_fun_body = {
                let impl_type_expr = params.ty_exprs()[0];

                let mut trait_impl_checks = Vec::new();
                for impl_did in tcx.all_impls(*task_key) {
                    let implementing_ty = tcx.type_of(impl_did).instantiate_identity();
                    let implementing_ty = RustTyDecomposition::from_ty(implementing_ty, impl_did);

                    let impl_type = deps.require_ref::<TyConstructorEnc>(implementing_ty.ty)?;

                    let type_check = vcx.mk_adt_discriminator_expr(
                        impl_type_expr,
                        impl_type.ty_constructor.name().to_str(),
                    );
                    trait_impl_checks.push(type_check);
                }

                // Check for types outside of the known type enumeration
                let unknown_type_check = {
                    let type_check = vcx.mk_adt_discriminator_expr(impl_type_expr, "Unknown_type");
                    let unknown_type_destructor =
                        vcx.mk_adt_destructor("non_unit", vir::TYPE_TYVAL, vir::TYPE_INT);
                    let unknown_type_id = unknown_type_destructor.call()(impl_type_expr);
                    vcx.mk_conj(&[type_check, impl_fun_unknown_idn(unknown_type_id)])
                };
                trait_impl_checks.push(unknown_type_check);

                vcx.mk_disj(&trait_impl_checks)
            };

            let impl_fun = vcx.mk_function(
                impl_fun_idn,
                (params.ty_decls(),),
                &[],
                &[],
                None,
                Some(impl_fun_body),
            );

            let trait_domain = vcx.mk_domain(
                vir_format_identifier!(vcx, "t_{trait_name}"),
                &[],
                &[],
                vcx.alloc_slice(funcs.as_slice()),
                None,
            );
            Ok((
                TraitEncOutput {
                    trait_domain,
                    impl_fun,
                    impl_fun_unknown,
                },
                TraitData {
                    trait_name,
                    type_did_fun_mapping,
                    impl_fun: impl_fun_idn,
                },
            ))
        })
    }
}
