use prusti_rustc_interface::{
    middle::{
        mir::{self, HasLocalDecls},
        ty::{self, GenericArg, List, FnSig, Binder},
    },
    span::def_id::DefId,
};
use task_encoder::TaskEncoderDependencies;

use crate::encoders::{
    lifted::{
        cast::{CastArgs, CastToEnc}, casters::CastTypePure, func_app_ty_params::LiftedFuncAppTyParamsEnc
    }, FunctionCallTaskDescription, PureFunctionEnc
};

/// Encoders (such as [`crate::encoders::MirPureEnc`],
/// [`crate::encoders::MirImpureEnc`]) implement this trait to encode
/// applications of Rust functions annotated as pure.
pub trait PureFuncAppEnc<'tcx: 'vir, 'vir> {
    /// Extra arguments required for the encoder to encode an argument to the
    /// function (in mir this is an `Operand`)
    type EncodeOperandArgs;

    /// The `Curr` in the resulting `ExprGen<'vir, Curr, Next>` type
    type Curr;

    /// The `Next` in the resulting `ExprGen<'vir, Curr, Next>` type
    type Next;

    /// The type of the data source that can provide local declarations; this is used
    /// when getting the type of the function.
    type LocalDeclsSrc: ?Sized + HasLocalDecls<'tcx>;

    // Are we monomorphizing functions?
    fn monomorphize(&self) -> bool;

    /// Task encoder dependencies are required for encoding Viper casts between
    /// generic and concrete types.
    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir>;

    /// The data source that can provide local declarations, necesary for determining
    /// the function type
    fn local_decls_src(&self) -> &Self::LocalDeclsSrc;
    fn vcx(&self) -> &'vir vir::VirCtxt<'tcx>;

    /// Encodes an operand (an argument to a function) as a pure Viper expression.
    fn encode_operand(
        &mut self,
        args: &Self::EncodeOperandArgs,
        operand: &mir::Operand<'tcx>,
    ) -> vir::ExprGen<'vir, Self::Curr, Self::Next>;

    /// Obtains the function's definition ID and the substitutions made at the callsite
    fn get_def_id_and_caller_substs(
        &self,
        func: &mir::Operand<'tcx>,
    ) -> (DefId, &'tcx List<GenericArg<'tcx>>) {
        let func_ty = func.ty(self.local_decls_src(), self.vcx().tcx());
        match func_ty.kind() {
            &ty::TyKind::FnDef(def_id, arg_tys) => (def_id, arg_tys),
            _ => todo!(),
        }
    }

    /// Encodes the arguments to the function. The first arguments are the lifted
    /// type parameters, followed by the actual arguments. Appropriate casts
    /// are inserted to convert from/to generic and concrete arguments as necessary.
    fn encode_fn_args(
        &mut self,
        sig: Binder<'tcx, FnSig<'tcx>>,
        substs: &'tcx List<GenericArg<'tcx>>,
        args: &[mir::Operand<'tcx>],
        encode_operand_args: &Self::EncodeOperandArgs,
    ) -> Vec<vir::ExprGen<'vir, Self::Curr, Self::Next>> {
        let mono = self.monomorphize();
        let fn_arg_tys = sig
            .inputs()
            .iter()
            .map(|i| i.skip_binder())
            .copied()
            .collect::<Vec<_>>();
        let encoded_ty_args = self
            .deps()
            .require_local::<LiftedFuncAppTyParamsEnc>(
                (mono, substs)
            )
            .unwrap();

        // Initial arguments are lifted type parameters
        let mut encoded_args = encoded_ty_args
            .iter()
            .map(|ty| ty.expr(self.vcx()))
            .collect::<Vec<_>>();

        let mut encoded_fn_args = fn_arg_tys
            .into_iter()
            .zip(args.iter())
            .map(|(expected_ty, oper)| {
                let base = self.encode_operand(encode_operand_args, oper);
                let oper_ty = oper.ty(self.local_decls_src(), self.vcx().tcx());
                let caster = self
                    .deps()
                    .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                        expected: expected_ty,
                        actual: oper_ty
                    })
                    .unwrap();
                caster.apply_cast_if_necessary(self.vcx(), base)
            })
            .collect::<Vec<_>>();

        encoded_args.append(&mut encoded_fn_args);
        encoded_args
    }

    /// Encodes the function application. The resulting application is casted
    /// to the appropriate generic/concrete type to match the type of `destination`.
    fn encode_pure_func_app(
        &mut self,
        def_id: DefId,
        sig: Binder<'tcx, FnSig<'tcx>>,
        substs: &'tcx List<GenericArg<'tcx>>,
        args: &Vec<mir::Operand<'tcx>>,
        destination: &mir::Place<'tcx>,
        caller_def_id: DefId,
        encode_operand_args: &Self::EncodeOperandArgs,
    ) -> vir::ExprGen<'vir, Self::Curr, Self::Next> {
        let vcx = self.vcx();
        let fn_result_ty = sig.output().skip_binder();
        let pure_func = self
            .deps()
            .require_ref::<PureFunctionEnc>(FunctionCallTaskDescription::new(def_id, substs, caller_def_id))
            .unwrap()
            .function_ref;
        let encoded_args = self.encode_fn_args(sig, substs, args, encode_operand_args);
        let call = pure_func.apply(vcx, &encoded_args);
        let expected_ty = destination.ty(self.local_decls_src(), vcx.tcx()).ty;
        let result_cast = self
            .deps()
            .require_ref::<CastToEnc<CastTypePure>>(CastArgs {
                expected: expected_ty,
                actual: fn_result_ty,
            })
            .unwrap();
        result_cast.apply_cast_if_necessary(vcx, call)
    }
}
