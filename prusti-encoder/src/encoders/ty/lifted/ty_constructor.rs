use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{CallableIdn, CastType, FunctionIdn, HasType};

use crate::encoders::ty::{
    RustTy, Sizedness,
    generics::{GArgs, GArgsTyEnc, GenericParamsEnc, traits::TraitEnc},
};

use super::r#typeof::{TypeOfEnc, TypeOfEncOutputRef};

#[derive(Debug, Clone)]
pub struct TyConstructorEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub ty_constructor: vir::FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>,

    /// Accessors of the arguments to an instantiation of the type constructor.
    /// Each function takes as input an instantiated type. The `i`th function in
    /// this list returns the `i`th argument to the type constructor.
    pub ty_param_accessors: &'vir [vir::AdtDestructor<'vir, vir::TyVal, vir::TyVal>],

    /// Accessors of the const parameters to an instantiation of the type constructor.
    /// Each function takes as input an instantiated type. The `i`th function in
    /// this list returns the `i`th const argument to the type constructor.
    pub const_param_accessors: &'vir [vir::AdtDestructor<'vir, vir::TyVal, vir::CSnap>],

    pub typeof_data: TypeOfEncOutputRef<'vir>,
}

impl<'vir> TyConstructorEncOutputRef<'vir> {
    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of its type.
    pub fn ty_param_from_snap(
        &self,
        idx: usize,
        snap: vir::ExprCSnap<'vir>,
    ) -> vir::ExprTyVal<'vir> {
        self.ty_param_accessors[idx].call()((self.typeof_data.typeof_function)(snap.upcast_ty()))
    }

    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th const parameter of its type.
    pub fn const_param_from_snap(
        &self,
        idx: usize,
        snap: vir::ExprCSnap<'vir>,
    ) -> vir::ExprCSnap<'vir> {
        self.const_param_accessors[idx].call()((self.typeof_data.typeof_function)(snap.upcast_ty()))
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

#[derive(Debug, Clone)]
pub struct TyConstructorEncOutput<'vir> {
    constructor: vir::AdtConstructor<'vir>,
    sized_check: Option<vir::ExprBool<'vir>>,
}

/// Encodes the lifted representation of a Rust type constructor (e.g. Option,
/// Vec, user-defined ADTs).
pub struct TyConstructorEnc;

impl TaskEncoder for TyConstructorEnc {
    task_encoder::encoder_cache!(TyConstructorEnc);
    type TaskDescription<'tcx> = RustTy<'tcx>;

    type OutputRef<'vir> = TyConstructorEncOutputRef<'vir>;

    type OutputFullLocal<'vir> = TyConstructorEncOutput<'vir>;

    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        assert!(!task_key.specifics.is_param());
        vir::with_vcx(|vcx| {
            let base_name = task_key.name();
            let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
            let type_function_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{base_name}_type",),
                (params.ty_args(), params.const_args()),
                vir::TYPE_TYVAL,
            );

            let ty_accessor_functions = params
                .ty_decls()
                .iter()
                .map(|param| {
                    vcx.mk_adt_destructor(
                        vir::vir_format!(vcx, "s_{base_name}_typaram_{}", param.name),
                        vir::TYPE_TYVAL,
                        param.ty(),
                    )
                })
                .collect::<Vec<_>>();
            let const_accessor_functions = params
                .const_decls()
                .iter()
                .map(|param| {
                    vcx.mk_adt_destructor(
                        vir::vir_format!(vcx, "s_{base_name}_constparam_{}", param.name),
                        vir::TYPE_TYVAL,
                        param.ty(),
                    )
                })
                .collect::<Vec<_>>();

            let typeof_data = deps.require_ref::<TypeOfEnc>(*task_key)?;
            deps.emit_output_ref(
                *task_key,
                TyConstructorEncOutputRef {
                    typeof_data,
                    ty_constructor: type_function_ident,
                    ty_param_accessors: vcx.alloc_slice(&ty_accessor_functions),
                    const_param_accessors: vcx.alloc_slice(&const_accessor_functions),
                },
            )?;

            let args = ty_accessor_functions
                .iter()
                .map(|d| vcx.mk_local_decl(d.name, d.ty).upcast_ty())
                .chain(
                    const_accessor_functions
                        .iter()
                        .map(|d| vcx.mk_local_decl(d.name, d.ty).upcast_ty()),
                )
                .collect::<Vec<vir::LocalDecl<vir::Dyn>>>();
            let constructor =
                vcx.mk_adt_constructor(type_function_ident.name().to_str(), vcx.alloc_slice(&args));
            let sized_check = {
                // Use a local expression named "Self" to build the function body
                let self_decl = vcx.mk_local_decl("Self$0", vir::TYPE_TYVAL);
                let self_expr = vcx.mk_local_ex(self_decl);
                let is_this_type =
                    vcx.mk_adt_discriminator_expr(self_expr, type_function_ident.name().to_str());

                let sized_impl_fun_idn: FunctionIdn<'vir, vir::TyVal, vir::Bool> = FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "Sized_impl"),
                    vir::TYPE_TYVAL,
                    vir::TYPE_BOOL,
                );
                match task_key.sizedness {
                    Sizedness::Sized => Some(is_this_type),
                    Sizedness::Unsized => None,
                    Sizedness::Dependent(ty) => match ty.kind() {
                        ty::TyKind::Param(param) => {
                            let accessor = ty_accessor_functions[param.index as usize];
                            let param_ty = accessor.call()(self_expr);
                            Some(
                                vir::expr! { vcx; (is_this_type) && ([sized_impl_fun_idn](param_ty)) },
                            )
                        }
                        ty::TyKind::Alias(ty::AliasTyKind::Projection, alias_ty) => {
                            let alias_did = alias_ty.def_id;
                            let trait_def = alias_ty.trait_def_id(vcx.tcx());
                            let trait_ = deps.require_ref::<TraitEnc>(trait_def)?;
                            let projection_fun = trait_.funs.assoc_types[&alias_did];
                            let args = deps.require_dep::<GArgsTyEnc>(GArgs::new(
                                task_key.params,
                                alias_ty.args,
                            ))?;
                            let inner_expr = vir::expr! { vcx;
                                (is_this_type) && ([sized_impl_fun_idn](
                                    [projection_fun]([..[args.get_ty()]], [..[args.get_const()]])
                                ))
                            };
                            let with_consts_bound = params.const_decls().iter().enumerate().rfold(
                                inner_expr,
                                |expr, (i, decl)| {
                                    let accessor = const_accessor_functions[i];
                                    vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                                },
                            );
                            let with_tys_bound = params.ty_decls().iter().enumerate().rfold(
                                with_consts_bound,
                                |expr, (i, decl)| {
                                    let accessor = ty_accessor_functions[i];
                                    vcx.mk_let_expr(decl, accessor.call()(self_expr), expr)
                                },
                            );
                            Some(with_tys_bound)
                        }
                        _ => panic!("Unsupported dependent sizedness for {ty:?}"),
                    },
                }
            };
            Ok((
                TyConstructorEncOutput {
                    constructor,
                    sized_check,
                },
                (),
            ))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let (mut constructors, sized_checks): (Vec<_>, Vec<_>) =
            Self::all_outputs_local_no_errors()
                .into_iter()
                .map(|out| (out.constructor, out.sized_check))
                .unzip();
        let mut sized_checks = sized_checks.into_iter().flatten().collect::<Vec<_>>();
        vir::with_vcx(|vcx| {
            let args = vcx.alloc_array(&[vcx.mk_local_decl("non_unit", vir::TYPE_INT)]);
            let unknown = vcx.mk_adt_constructor("Unknown_type", args);
            constructors.push(unknown);
            let adt = vcx.mk_adt(
                vir::ViperIdent::new("Type"),
                &[],
                vcx.alloc_slice(&constructors),
            );
            program.add_adt(adt);

            // Since we know all type constructors now, we can emit the `Sized` trait
            let sized_impl_fun_idn: FunctionIdn<'vir, vir::TyVal, vir::Bool> = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "Sized_impl"),
                vir::TYPE_TYVAL,
                vir::TYPE_BOOL,
            );
            let sized_impl_unknown_fun_idn: FunctionIdn<'vir, vir::Int, vir::Bool> =
                FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "Sized_unknown_impl"),
                    vir::TYPE_INT,
                    vir::TYPE_BOOL,
                );

            let self_decl = vcx.mk_local_decl("Self$0", vir::TYPE_TYVAL);
            let unknown_type_check = {
                let self_expr = vcx.mk_local_ex(self_decl);
                let is_unknown_type = vcx.mk_adt_discriminator_expr(self_expr, "Unknown_type");

                let unknown_id_destructor =
                    vcx.mk_adt_destructor("non_unit", vir::TYPE_TYVAL, vir::TYPE_INT);
                let extracted_id = unknown_id_destructor.call()(self_expr);

                vir::expr! {vcx; (is_unknown_type) && ([sized_impl_unknown_fun_idn](extracted_id)) }
            };

            sized_checks.push(unknown_type_check);
            let sized_impl_fun = vcx.mk_function(
                sized_impl_fun_idn,
                (self_decl,),
                &[],
                &[],
                None,
                Some(vcx.mk_disj(&sized_checks)),
            );

            program.add_function(sized_impl_fun);

            let sized_impl_unknown_fun = vcx.mk_function(
                sized_impl_unknown_fun_idn,
                (vcx.mk_local_decl("non_unit", vir::TYPE_INT),),
                &[],
                &[],
                None,
                None,
            );
            program.add_function(sized_impl_unknown_fun);
        })
    }
}
