use task_encoder::{EncodeFullResult, OutputRefAny, TaskEncoder};
use vir::{vir_format_identifier, Arity, CallableIdn, CastType, FunctionIdn};

use crate::encoders::{
    domain::DomainEnc,
    most_generic_ty::{extract_type_params, MostGenericTy},
    GenericEnc,
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

    /// Returns the Viper representation of the type of a snapshot-encoded value
    pub typeof_function: vir::FunctionIdn<'vir, vir::CSnap, vir::TyVal>,
}

impl<'vir> TyConstructorEncOutputRef<'vir> {
    pub fn arity(&self) -> <vir::ManyTyVal as Arity>::Tys<'vir> {
        self.ty_constructor.arity()
    }

    pub fn args(&self) -> impl Iterator<Item = vir::TypeTyVal<'vir>> + '_ {
        self.arity().into_iter().copied()
    }

    /// Takes as input a snapshot encoding of a rust value, and returns
    /// the `idx`th type parameter of it's type.
    pub fn ty_param_from_snap(
        &self,
        vcx: &'vir vir::VirCtxt,
        idx: usize,
        snap: vir::ExprCSnap<'vir>,
    ) -> vir::ExprTyVal<'vir> {
        self.ty_param_accessors[idx].call()((self.typeof_function)(snap))
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct TyConstructorEncOutput<'vir> {
    pub variant: vir::AdtConstructor<'vir>,
    pub typeof_function: vir::DomainFunction<'vir>,
}

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
        let generic_ref = deps.require_ref::<GenericEnc>(())?;
        vir::with_vcx(|vcx| {
            let (ty_constructor, _) = extract_type_params(vcx.tcx(), task_key.ty());
            let base_name = ty_constructor.get_vir_base_name(vcx);
            let args = ty_constructor.generics();
            let type_function_args = vcx.alloc_slice(&vec![generic_ref.type_snapshot; args.len()]);
            let type_function_ident = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{base_name}_type",),
                type_function_args,
                generic_ref.type_snapshot,
            );

            let ty_accessor_functions = args
                .iter()
                .map(|arg| {
                    vcx.mk_adt_destructor(
                        vir::vir_format!(vcx, "s_{base_name}_typaram_{}", arg.name),
                        generic_ref.type_snapshot,
                        generic_ref.type_snapshot,
                    )
                })
                .collect::<Vec<_>>();

            let domain = deps.require_ref::<DomainEnc>(*task_key)?;
            let snap = (domain.domain)().downcast_ty();
            let typeof_function = FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{base_name}_typeof"),
                snap,
                generic_ref.type_snapshot,
            );
            deps.emit_output_ref(
                *task_key,
                TyConstructorEncOutputRef {
                    typeof_function,
                    ty_constructor: type_function_ident,
                    ty_param_accessors: vcx.alloc_slice(&ty_accessor_functions),
                },
            )?;

            let args = ty_accessor_functions.iter().map(|d|
                vcx.mk_local_decl(d.name, d.ty)
            ).collect::<Vec<_>>();
            let variant = vcx.mk_adt_constructor(type_function_ident.name().to_str(), vcx.alloc_slice(&args));
            let typeof_function = vcx.mk_domain_function(typeof_function, false);
            let result = TyConstructorEncOutput {
                variant,
                typeof_function,
            };
            Ok((result, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let all = Self::all_outputs_local();
        vir::with_vcx(|vcx| {
            let mut typeof_fns = Vec::new();
            let args = vcx.alloc_array(&[vcx.mk_local_decl("non_unit", vir::TYPE_INT)]);
            let unknown = vcx.mk_adt_constructor("Unknown_type", args);
            let constructors = all
                .into_iter()
                .map(|output| {
                    typeof_fns.push(output.typeof_function);
                    output.variant
                })
                .chain([unknown])
                .collect::<Vec<_>>();
            let adt = vcx.mk_adt(vir::ViperIdent::new("Type"), &[], vcx.alloc_slice(&constructors));
            program.add_adt(adt);
            let domain = vcx.mk_domain(vir::ViperIdent::new("TypeOf"), &[], &[], vcx.alloc_slice(&typeof_fns));
            program.add_domain(domain);
        })
    }
}
