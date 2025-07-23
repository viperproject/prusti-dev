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
    pub ty_param_accessors: &'vir [vir::FunctionIdn<'vir, vir::TyVal, vir::TyVal>],

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
        self.ty_param_accessors[idx]((self.typeof_function)(snap))
    }
}

impl<'vir> OutputRefAny for TyConstructorEncOutputRef<'vir> {}

#[derive(Clone)]
pub struct TyConstructorEncOutput<'vir> {
    pub domain: vir::Domain<'vir>,
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
        let mut functions = vec![];
        let mut axioms = vec![];
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
            functions.push(vcx.mk_domain_function(type_function_ident, false));
            let ty_arg_decls: Vec<vir::LocalDeclTyVal<'vir>> = args
                .iter()
                .enumerate()
                .map(|(idx, _)| {
                    vcx.mk_local_decl(
                        vcx.alloc_str(&format!("arg_{}", idx)),
                        generic_ref.type_snapshot,
                    )
                })
                .collect();
            let ty_arg_exprs: Vec<vir::ExprTyVal<'vir>> = ty_arg_decls
                .iter()
                .map(|decl| vcx.mk_local_ex(decl.name, decl.ty))
                .collect::<Vec<_>>();
            let func_app = type_function_ident(ty_arg_exprs.as_slice());

            let ty_accessor_functions = args
                .iter()
                .map(|arg| {
                    FunctionIdn::new(
                        vir::vir_format_identifier!(vcx, "s_{base_name}_typaram_{}", arg.name),
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
            functions.push(vcx.mk_domain_function(typeof_function, false));
            deps.emit_output_ref(
                *task_key,
                TyConstructorEncOutputRef {
                    typeof_function,
                    ty_constructor: type_function_ident,
                    ty_param_accessors: vcx.alloc_slice(&ty_accessor_functions),
                },
            )?;

            let axiom_qvars = vcx.alloc_slice(&ty_arg_decls);
            let axiom_triggers = vcx.alloc_slice(&[vcx.mk_trigger(&[func_app])]);
            for (accessor_function, ty_arg) in ty_accessor_functions.iter().zip(ty_arg_exprs.iter())
            {
                functions.push(vcx.mk_domain_function(*accessor_function, false));
                axioms.push(vcx.mk_domain_axiom(
                    vir::vir_format_identifier!(vcx, "ax_{}", accessor_function.name()),
                    vcx.mk_forall_expr(
                        axiom_qvars,
                        axiom_triggers,
                        vcx.mk_eq_expr(accessor_function(func_app), ty_arg),
                    ),
                ))
            }
            let result = TyConstructorEncOutput {
                domain: vcx.mk_domain(
                    vir_format_identifier!(
                        vcx,
                        "s_{}_ty_constructor",
                        task_key.get_vir_base_name(vcx)
                    ),
                    &[],
                    vcx.alloc_slice(&axioms),
                    vcx.alloc_slice(&functions),
                ),
            };
            Ok((result, ()))
        })
    }
}
