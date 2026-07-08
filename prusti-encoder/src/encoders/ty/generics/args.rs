use prusti_rustc_interface::middle::ty;

use super::GParams;

/// The instantiation of generic arguments, typically found in `TyKind::Adt` and
/// `TyKind::FnDef`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
pub struct GArgs<'tcx> {
    pub(super) context: GParams<'tcx>,
    pub(super) args: &'tcx [ty::GenericArg<'tcx>],
}

pub enum GParamVariant<'tcx> {
    Param(ty::ParamTy),
    Alias(ty::AliasTy<'tcx>),
}

impl<'tcx> GArgs<'tcx> {
    pub fn new(context: impl Into<GParams<'tcx>>, args: &'tcx [ty::GenericArg<'tcx>]) -> Self {
        let context: GParams<'tcx> = context.into();
        // Sanity check that all generic values in args are bound (i.e. defined
        // in context).
        for arg in args.iter().flat_map(|arg| arg.walk()) {
            let valid = context.check_arg(arg);
            assert!(valid, "context: {context:#?}, args: {args:#?}");
        }
        GArgs { context, args }
    }

    pub fn context(self) -> GParams<'tcx> {
        self.context
    }

    pub fn args(self) -> &'tcx [ty::GenericArg<'tcx>] {
        self.args
    }

    /// Drops the generic context, keeping the (ground) `args`. Use when the
    /// context is irrelevant to the encoding (e.g. a builtin's concrete result
    /// type) so that clients in different contexts (different where-clauses)
    /// share one task key. Panics (via `new`) if the `args` are not ground.
    pub fn with_empty_context(self) -> Self {
        Self::new(GParams::empty(), self.args)
    }

    /// Substitutes type arguments and try to normalize associated types
    pub fn normalize(self, ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
        // Substitute type parameters
        let ty = vir::with_vcx(|vcx| ty::EarlyBinder::bind(ty).instantiate(vcx.tcx(), self.args));
        // Normalize associated types
        self.context.normalize(ty)
    }

    pub fn expect_param(self) -> GParamVariant<'tcx> {
        assert_eq!(self.args.len(), 1);
        match self.args[0].expect_ty().kind() {
            ty::TyKind::Param(p) => GParamVariant::Param(*p),
            ty::TyKind::Alias(_k, t) => GParamVariant::Alias(*t),
            other => panic!("expected type parameter, {other:?}"),
        }
    }

    /// Given the definitions:
    /// ```
    /// struct S0<'a, T0, U0>
    /// struct S1<'a, T1, U1> {
    ///     field: S0<'a, U1, T1>,
    /// }
    /// # { field: &'a mut T }
    /// fn foo<'x>(x: S1<'x, u32, bool>)
    /// # {}
    /// ```
    /// We will decompose `S1<'x, u32, bool>` into a `GArgs` of `['x, u32, bool]`.
    /// When traversing into the definition of `S1`, the field `S0<'a, U1, T1>` is
    /// decomposed into a `GArgs` of `['a, U1, T1]`. This function will substitute
    /// the first into the second resulting in the `GArgs` of `['x, bool, u32]`.
    /// This is useful when encoding the field of `S1` in the context of `foo`
    /// (without any e.g. predicate that needs to be general for any use of `S1`).
    pub fn substitute(self, to_sub_in: GArgs<'tcx>) -> GArgs<'tcx> {
        assert_eq!(self.context.rust_params().len(), to_sub_in.args.len());
        let args = vir::with_vcx(|vcx| {
            let args = self
                .args
                .iter()
                .map(|arg| ty::EarlyBinder::bind(*arg).instantiate(vcx.tcx(), to_sub_in.args));
            vcx.tcx().mk_args_from_iter(args)
        });
        GArgs {
            context: to_sub_in.context,
            args,
        }
    }
}
