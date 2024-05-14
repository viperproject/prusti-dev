use prusti_rustc_interface::
    middle::{mir, ty::Ty}
;
use task_encoder::{TaskEncoder, TaskEncoderDependencies};
use vir::{CallableIdent, ExprGen, FunctionIdent, Reify, UnknownArity, ViperIdent};

use crate::encoders::{
    domain::DomainEnc, lifted::{func_def_ty_params::LiftedTyParamsEnc, ty::{EncodeGenericsAsLifted, LiftedTy, LiftedTyEnc}}, most_generic_ty::extract_type_params, GenericEnc, MirLocalDefEnc, MirPureEnc, MirPureEncTask, MirSpecEnc, PureKind
};

use super::function_enc::FunctionEnc;

#[derive(Clone, Debug)]
pub struct MirFunctionEncOutputRef<'vir> {
    pub function_ref: FunctionIdent<'vir, UnknownArity<'vir>>,
}
impl<'vir> task_encoder::OutputRefAny for MirFunctionEncOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct MirFunctionEncOutput<'vir> {
    pub function: vir::Function<'vir>,
}

/// Task encoders can implement this trait to encode pure functions. We use this
/// code to support sharing code between monomorphic and polymorphic encoding of
/// functions; see [`MirMonoFunctionEnc`] and [`MirFunctionEnc`]
pub trait PureFunctionEnc
where
    Self: 'static + Sized + FunctionEnc + for <'vir> TaskEncoder<
        OutputRef<'vir> = MirFunctionEncOutputRef<'vir>
    >
{

    /// Generates the identifier for the function; for a monomorphic encoding,
    /// this should be a name including (mangled) type arguments
    fn mk_function_ident<'vir, 'tcx>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        task_key: &Self::TaskKey<'tcx>,
    ) -> ViperIdent<'vir>;


    /// Adds an assertion connecting the type of an argument (or return) of the
    /// function with the appropriate type based on the param, e.g. in f<T,
    /// U>(u: U) -> T, this would be called to require that the type of `u` be
    /// `U`
    fn mk_type_assertion<'vir, 'tcx: 'vir, Curr, Next>(
        vcx: &'vir vir::VirCtxt<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
        arg: ExprGen<'vir, Curr, Next>, // Snapshot encoded argument
        ty: Ty<'tcx>,
    ) -> Option<ExprGen<'vir, Curr, Next>> {
        let lifted_ty = deps
            .require_local::<LiftedTyEnc<EncodeGenericsAsLifted>>(ty)
            .unwrap();
        match lifted_ty {
            LiftedTy::Generic(generic) => {
                let generic_enc = deps.require_ref::<GenericEnc>(()).unwrap();
                Some(vcx.mk_eq_expr(
                    generic_enc.param_type_function.apply(vcx, [arg]),
                    generic.expr(vcx),
                ))
            }
            // When the instantiated type constructor doesn't take any
            // arguments, the type of the argument is known by the
            // definition of its `typeof_funtion`, therefore it's not
            // necessary to include an explicit assertion
            LiftedTy::Instantiated { args, .. } if !args.is_empty() => {
                let domain_ref = deps
                    .require_ref::<DomainEnc>(extract_type_params(vcx.tcx(), ty).0)
                    .unwrap();
                Some(vcx.mk_eq_expr(
                    domain_ref.typeof_function.apply(vcx, [arg]),
                    lifted_ty.expr(vcx),
                ))
            }
            _ => None,
        }
    }

    fn encode<'vir, 'tcx: 'vir>(
        task_key: Self::TaskKey<'tcx>,
        deps: &mut TaskEncoderDependencies<'vir>,
    ) -> MirFunctionEncOutput<'vir> {
        let def_id = Self::get_def_id(&task_key);
        let caller_def_id = Self::get_caller_def_id(&task_key);
        let trusted = crate::encoders::with_proc_spec(def_id, |def_spec| {
            def_spec.trusted.extract_inherit().unwrap_or_default()
        })
        .unwrap_or_default();
        vir::with_vcx(|vcx| {
            let substs = Self::get_substs(vcx, &task_key);
            let local_defs = deps
                .require_local::<MirLocalDefEnc>((def_id, substs, caller_def_id))
                .unwrap();

            tracing::debug!("encoding {def_id:?}");

            let function_ident = Self::mk_function_ident(vcx, &task_key);
            let ty_arg_decls = deps.require_local::<LiftedTyParamsEnc>(substs).unwrap();
            let mut ident_args = ty_arg_decls.iter().map(|arg| arg.ty()).collect::<Vec<_>>();
            ident_args.extend(
                (1..=local_defs.arg_count)
                    .map(mir::Local::from)
                    .map(|def_idx| local_defs.locals[def_idx].ty.snapshot),
            );
            let ident_args = UnknownArity::new(vcx.alloc_slice(&ident_args));
            let return_type = local_defs.locals[mir::RETURN_PLACE].ty;
            let function_ref = FunctionIdent::new(function_ident, ident_args, return_type.snapshot);
            deps.emit_output_ref::<Self>(task_key, MirFunctionEncOutputRef { function_ref });

            let spec = deps
                .require_local::<MirSpecEnc>((def_id, substs, None, true))
                .unwrap();

            let mut func_args = ty_arg_decls
                .iter()
                .map(|arg| arg.decl())
                .collect::<Vec<_>>();

            func_args.extend((1..=local_defs.arg_count).map(mir::Local::from).map(|arg| {
                vcx.alloc(vir::LocalDeclData {
                    name: local_defs.locals[arg].local.name,
                    ty: local_defs.locals[arg].ty.snapshot,
                })
            }));

            let expr = if trusted {
                None
            } else {
                // Encode the body of the function
                let expr = deps
                    .require_local::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: 0,
                        kind: PureKind::Pure,
                        parent_def_id: def_id,
                        param_env: vcx.tcx().param_env(def_id),
                        substs,
                        caller_def_id,
                    })
                    .unwrap()
                    .expr;
                let expr = expr.reify(vcx, (def_id, spec.pre_args));
                assert!(
                    expr.ty() == return_type.snapshot,
                    "expected {:?}, got {:?}",
                    return_type.snapshot,
                    expr.ty()
                );
                Some(expr)
            };
            let sig = vcx.tcx().subst_and_normalize_erasing_regions(
                substs,
                vcx.tcx().param_env(def_id),
                vcx.tcx().fn_sig(def_id),
            );
            let input_tys = sig
                .inputs()
                .iter()
                .map(|i| i.skip_binder())
                .copied()
                .collect::<Vec<_>>();
            let type_preconditions = input_tys.iter().enumerate().filter_map(|(idx, ty)| {
                let vir_arg = local_defs.locals[mir::Local::from(idx + 1)];
                let vir_arg = vcx.mk_local_ex(vir_arg.local.name, vir_arg.ty.snapshot);
                Self::mk_type_assertion(vcx, deps, vir_arg, *ty)
            });

            tracing::debug!("finished {def_id:?}");

            let mut pres = spec.pres;
            pres.extend(type_preconditions);

            let type_postcondition = Self::mk_type_assertion(
                vcx,
                deps,
                vcx.mk_result(return_type.snapshot),
                sig.output().skip_binder(),
            );
            let mut posts = spec.posts;
            if let Some(pc) = type_postcondition {
                posts.push(pc);
            }

            MirFunctionEncOutput {
                function: vcx.mk_function(
                    function_ident.to_str(),
                    vcx.alloc_slice(&func_args),
                    return_type.snapshot,
                    vcx.alloc_slice(&pres),
                    vcx.alloc_slice(&posts),
                    expr,
                ),
            }
        })
    }
}
