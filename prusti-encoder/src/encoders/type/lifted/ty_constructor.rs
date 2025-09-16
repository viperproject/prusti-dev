use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{Arity, CallableIdn, CastType, FunctionIdn};

use crate::encoders::{
    lifted::r#typeof::{TypeOfEnc, TypeOfEncOutputRef}, most_generic_ty::{MostGenericTy, MostGenericTyEnc}
};

#[derive(Clone)]
pub struct TyConstructorEncOutputRef<'vir> {
    /// Takes as input the generics for this type (if any),
    /// and returns the resulting type
    pub ty_constructor: vir::FunctionIdn<'vir, vir::ManyTyVal, vir::TyVal>,

    /// Accessors of the arguments to an instantiation of the type constructor.
    /// Each function takes as input an instantiated type. The `i`th function in
    /// this list returns the `i`th argument to the type constructor.
    pub ty_param_accessors: &'vir [vir::AdtDestructor<'vir, vir::TyVal, vir::TyVal>],

    pub typeof_data: TypeOfEncOutputRef<'vir>,
}

impl<'vir> TyConstructorEncOutputRef<'vir> {
    pub fn arity(&self) -> <vir::ManyTyVal as Arity>::Tys<'vir> {
        self.ty_constructor.arity()
    }

    pub fn args(&self) -> impl Iterator<Item = vir::TypeTyVal<'vir>> + '_ {
        self.arity().into_iter().copied()
    }

    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of its type.
    pub fn ty_param_from_snap(
        &self,
        vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::ExprCSnap<'vir>,
    ) -> vir::ExprTyVal<'vir> {
        self.ty_param_accessors[idx].call()((self.typeof_data.typeof_function)(snap.upcast_ty()))
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

pub type TyConstructorEncOutput<'vir> = vir::AdtConstructor<'vir>;

/// Encodes the lifted representation of a Rust type constructor (e.g. Option,
/// Vec, user-defined ADTs).
pub struct TyConstructorEnc;

impl TaskEncoder for TyConstructorEnc {
    task_encoder::encoder_cache!(TyConstructorEnc);
    type TaskDescription<'tcx> = MostGenericTy<'tcx>;

    type TaskKey<'tcx> = Self::TaskDescription<'tcx>;

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
        assert!(!task_key.is_generic());
        vir::with_vcx(|vcx| {
            let (generic_ty, _) = deps.require_local::<MostGenericTyEnc>(task_key.ty())?;
            let base_name = generic_ty.get_vir_base_name(vcx);
            let args = generic_ty.generics();
            let type_function_args = vcx.alloc_slice(&vec![vir::TYPE_TYVAL; args.len()]);
            let type_function_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{base_name}_type",),
                type_function_args,
                vir::TYPE_TYVAL,
            );

            let ty_accessor_functions = args
                .iter()
                .map(|arg| {
                    vcx.mk_adt_destructor(
                        vir::vir_format!(vcx, "s_{base_name}_typaram_{}", arg.name),
                        vir::TYPE_TYVAL,
                        vir::TYPE_TYVAL,
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
                },
            )?;

            let args = ty_accessor_functions.iter().map(|d|
                vcx.mk_local_decl(d.name, d.ty)
            ).collect::<Vec<_>>();
            let variant = vcx.mk_adt_constructor(type_function_ident.name().to_str(), vcx.alloc_slice(&args));
            Ok((variant, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let mut constructors = Self::all_outputs_local_no_errors();
        vir::with_vcx(|vcx| {
            let args = vcx.alloc_array(&[vcx.mk_local_decl("non_unit", vir::TYPE_INT)]);
            let unknown = vcx.mk_adt_constructor("Unknown_type", args);
            constructors.push(unknown);
            let adt = vcx.mk_adt(vir::ViperIdent::new("Type"), &[], vcx.alloc_slice(&constructors));
            program.add_adt(adt);
        })
    }
}
