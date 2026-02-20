use prusti_rustc_interface::middle::ty;

use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{CallableIdn, CastType, FunctionIdn, HasType};

use crate::encoders::ty::{
    RustTy, RustTyDecomposition, TySpecifics,
    generics::{GArgs, GParams, GenericParamsEnc},
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
    sized_check: vir::ExprBool<'vir>,
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
                let self_decl = vcx.mk_local_decl("Self", vir::TYPE_TYVAL);
                let self_expr = vcx.mk_local_ex(self_decl);
                let is_this_type =
                    vcx.mk_adt_discriminator_expr(self_expr, type_function_ident.name().to_str());

                let sized_impl_fun_idn: FunctionIdn<'vir, vir::TyVal, vir::Bool> = FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "Sized_impl"),
                    vir::TYPE_TYVAL,
                    vir::TYPE_BOOL,
                );

                let is_sized = {
                    let identity_args = GArgs::new(task_key.params, task_key.params.rust_params());
                    let decomp = RustTyDecomposition {
                        ty: *task_key,
                        args: identity_args,
                        maybe_inhabited: true,
                    };
                    check_sizedness(vcx.tcx(), decomp)
                };

                match is_sized {
                    Sizedness::Definite(true) => is_this_type,
                    Sizedness::Definite(false) => vir::expr! {vcx; false },
                    Sizedness::ParamDependent(param) => {
                        let param_idx = task_key
                            .params
                            .rust_params()
                            .iter()
                            .position(|p| p == param)
                            .unwrap();
                        let param_ty = ty_accessor_functions[param_idx].call()(self_expr);

                        vir::expr! { vcx; (is_this_type) == > ([sized_impl_fun_idn](param_ty)) }
                    }
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
        vir::with_vcx(|vcx| {
            vcx.tcx();
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
            // TODO: Correct implementation of `Sized`
            let sized_impl_fun_idn: FunctionIdn<'vir, vir::TyVal, vir::Bool> = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "Sized_impl"),
                vir::TYPE_TYVAL,
                vir::TYPE_BOOL,
            );
            let self_decl = vcx.mk_local_decl("Self", vir::TYPE_TYVAL);
            let sized_impl_fun = vcx.mk_function(
                sized_impl_fun_idn,
                (self_decl,),
                &[],
                &[],
                None,
                Some(vcx.mk_disj(&sized_checks)),
            );

            program.add_function(sized_impl_fun);
        })
    }
}

#[derive(Debug, Clone)]
enum Sizedness<'tcx> {
    Definite(bool),
    ParamDependent(ty::GenericArg<'tcx>),
}

fn check_sizedness<'a>(tcx: ty::TyCtxt<'a>, decomp: RustTyDecomposition<'a>) -> Sizedness<'a> {
    let ctx = decomp.args.context();
    if decomp
        .ty
        .rust_ty
        .is_some_and(|ty| ty.is_sized(tcx, ctx.typing_env()))
    {
        return Sizedness::Definite(true);
    }
    match &decomp.ty.specifics {
        TySpecifics::StructLike(data) => {
            // Only need to check the last field of the struct for unsizedness
            if let Some(last_field) = data.fields.last() {
                // The type is not definitely sized. Need to recurse on the field's type
                let normalized_decomp = last_field.ty().decompose_normalize(decomp.args);

                check_sizedness(tcx, normalized_decomp)
            } else {
                Sizedness::Definite(true) // Empty structs are Sized
            }
        }
        TySpecifics::Param(_) => Sizedness::ParamDependent(decomp.args.args()[0]),
        TySpecifics::ArrayLike(data) if data.slice => Sizedness::Definite(false),
        TySpecifics::Opaque(_) => unimplemented!("Is an opaque type sized?"),
        // Builtin, Enums, Primitives, References, and fixed-size Arrays are always Sized.
        _ => Sizedness::Definite(true),
    }
}
