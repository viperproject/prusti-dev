use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};

use super::{
    RustParamData, RustTy, RustTyDecomposition, TySpecifics,
    generics::{GArgsTy, GenericParamsEnc},
    lifted::TyConstructorEnc,
    pure::TyPureEnc,
    use_inhabited::TyUseInhabitedEnc,
};

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, TyInhabitedEnc>>;

#[derive(Debug, Clone, Copy)]
enum InhabitedTyRef<'vir> {
    GenericParam,
    Constructor(vir::FunctionIdn<'vir, (vir::ManyTyVal, vir::ManyCSnap), vir::TyVal>),
}

#[derive(Debug, Clone, Copy)]
pub struct TyInhabitedRef<'vir> {
    inhabited: vir::FunctionIdn<'vir, vir::TyVal, vir::Bool>,
    ty: InhabitedTyRef<'vir>,
}

impl<'vir> task_encoder::OutputRefAny for TyInhabitedRef<'vir> {}

impl<'vir> TyInhabitedRef<'vir> {
    pub fn apply<Curr, Next>(&self, args: GArgsTy<'vir>) -> vir::ExprGenBool<'vir, Curr, Next> {
        let ty: vir::ExprGenTyVal<'vir, Curr, Next> = match self.ty {
            InhabitedTyRef::GenericParam => {
                assert_eq!(args.get_ty::<Curr, Next>().len(), 1);
                assert!(args.get_const::<Curr, Next>().is_empty());
                args.get_ty::<Curr, Next>()[0]
            }
            InhabitedTyRef::Constructor(constructor) => {
                constructor.call()(args.get_ty::<Curr, Next>(), args.get_const::<Curr, Next>())
            }
        };
        self.inhabited.call()(ty)
    }
}

/// Encodes axioms that define when a Rust type is inhabited (relative to its
/// type parameters). This encoder takes a `RustTy` as input and therefore does
/// not consider actual type parameters a Rust type may be instantiated with. To
/// determine whether a type is inhabited (taking type parameters into account)
// `TyUseInhabitedEnc` should be used instead.
pub struct TyInhabitedEnc;

impl TaskEncoder for TyInhabitedEnc {
    task_encoder::encoder_cache!(TyInhabitedEnc);
    const ENCODER_NAME: &'static str = "type inhabitedness encoder";

    type TaskDescription<'vir> = RustTy<'vir>;
    type OutputRef<'vir> = TyInhabitedRef<'vir>;
    type OutputFullLocal<'vir> = Option<vir::DomainAxiom<'vir>>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let inhabited = Self::inhabited_fn();
            let ty = if matches!(
                task_key.specifics,
                TySpecifics::Param(RustParamData::Generic)
            ) {
                InhabitedTyRef::GenericParam
            } else {
                InhabitedTyRef::Constructor(
                    deps.require_ref::<TyConstructorEnc>(*task_key)?
                        .ty_constructor,
                )
            };
            let output_ref = TyInhabitedRef { inhabited, ty };

            deps.emit_output_ref(*task_key, output_ref)?;

            // No axiom should be emitted for fully generic parameters
            if matches!(ty, InhabitedTyRef::GenericParam) {
                return Ok((None, ()));
            }

            let params = deps.require_dep::<GenericParamsEnc>(task_key.params)?;
            let args = GArgsTy::new(
                vcx.alloc_slice(params.ty_exprs()),
                vcx.alloc_slice(params.const_exprs()),
            );
            let lhs = output_ref.apply(args);
            let rhs = InhabitedWalker { deps }.encode(task_key)?;
            let body = vcx.mk_eq_expr(lhs, rhs);
            let axiom_expr = if params.ty_decls().is_empty() && params.const_decls().is_empty() {
                body
            } else {
                vir::expr! {
                    forall ..[params.ty_decls()], ..[params.const_decls()] :: {[lhs]}
                        [body]
                }
            };
            let axiom = vcx.mk_domain_axiom(
                vir::vir_format_identifier!(vcx, "inhabited_{}", task_key.name()),
                axiom_expr,
            );
            Ok((Some(axiom), ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let axioms = Self::all_outputs_local_no_errors(program)
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        vir::with_vcx(|vcx| {
            let inhabited = vcx.mk_domain_function(Self::inhabited_fn(), false, None);
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("Inhabited"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&[inhabited]),
                None,
            );
            program.add_domain(domain);
        })
    }
}

impl TyInhabitedEnc {
    fn inhabited_fn<'vir>() -> vir::FunctionIdn<'vir, vir::TyVal, vir::Bool> {
        vir::FunctionIdn::new(
            vir::ViperIdent::new("inhabited"),
            vir::TYPE_TYVAL,
            vir::TYPE_BOOL,
        )
    }
}

struct InhabitedWalker<'a, 'vir> {
    deps: &'a mut TaskEncoderDependencies<'vir, TyInhabitedEnc>,
}

impl<'a, 'vir> InhabitedWalker<'a, 'vir> {
    fn encode(&mut self, ty: RustTy<'vir>) -> EncResult<'vir, vir::ExprBool<'vir>> {
        Ok(match &ty.specifics {
            TySpecifics::Param(RustParamData::Generic) => unreachable!(),
            TySpecifics::Param(RustParamData::Dyn)
            | TySpecifics::Opaque(_)
            | TySpecifics::Primitive(_)
            | TySpecifics::Raw(_)
            | TySpecifics::Builtin(_) => vir::with_vcx(|vcx| vcx.mk_bool::<true>()),
            TySpecifics::ImmRef(data) | TySpecifics::MutRef(data) => {
                self.encode_decomposition(data.referent.decompose(ty.params))?
            }
            TySpecifics::ArrayLike(data) => {
                if data.slice {
                    // An empty slice value exists even if its element type is uninhabited
                    vir::with_vcx(|vcx| vcx.mk_bool::<true>())
                } else {
                    let params = self.deps.require_dep::<GenericParamsEnc>(ty.params)?;
                    assert_eq!(params.const_exprs().len(), 1);
                    let usize_ty = vir::with_vcx(|vcx| vcx.tcx().types.usize);
                    let usize_enc = self
                        .deps
                        .require_dep::<TyPureEnc>(RustTyDecomposition::from_prim_ty(usize_ty).ty)?;
                    let usize_prim = usize_enc.expect_primitive();
                    let zero = usize_prim.prim_to_snap(usize_prim.expr_from_bits(usize_ty, 0));
                    let len_is_zero =
                        vir::with_vcx(|vcx| vcx.mk_eq_expr(params.const_exprs()[0], zero));
                    let element = self.encode_decomposition(data.data.decompose(ty.params))?;
                    vir::expr! { (len_is_zero) || (element) }
                }
            }
            TySpecifics::StructLike(data) => {
                let fields = data
                    .fields
                    .iter()
                    .map(|field| self.encode_decomposition(field.ty().decompose(ty.params)))
                    .collect::<EncResult<'vir, Vec<_>>>()?;
                vir::with_vcx(|vcx| vcx.mk_conj(&fields))
            }
            TySpecifics::EnumLike(data) => {
                let variants = data
                    .variants
                    .iter()
                    .map(|variant| {
                        let fields = variant
                            .inner
                            .fields
                            .iter()
                            .map(|field| self.encode_decomposition(field.ty().decompose(ty.params)))
                            .collect::<EncResult<'vir, Vec<_>>>()?;
                        Ok(vir::with_vcx(|vcx| vcx.mk_conj(&fields)))
                    })
                    .collect::<EncResult<'vir, Vec<_>>>()?;
                vir::with_vcx(|vcx| vcx.mk_disj(&variants))
            }
        })
    }

    fn encode_decomposition(
        &mut self,
        ty: RustTyDecomposition<'vir>,
    ) -> EncResult<'vir, vir::ExprBool<'vir>> {
        Ok(self.deps.require_ref::<TyUseInhabitedEnc>(ty)?.inhabited())
    }
}
