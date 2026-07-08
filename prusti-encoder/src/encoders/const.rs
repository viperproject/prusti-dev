use prusti_rustc_interface::{
    const_eval::{
        const_eval::{CompileTimeMachine, mk_eval_cx_for_const_val},
        interpret::{CtfeProvenance, InterpCx, Projectable},
    },
    middle::{
        mir::{
            self, ConstValue,
            interpret::{GlobalAlloc, Scalar},
        },
        ty,
        ty::TypingEnv,
    },
    span::{Span, def_id::DefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn};

use crate::encoders::{
    MirPureEnc, MirPureEncTask, PureKind,
    addr::RefDataEnc,
    ty::{
        RustTyDecomposition, TySpecifics,
        generics::{GParams, GenericParamsEnc},
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum ConstEncTask<'vir> {
    Ty {
        const_: ty::Const<'vir>,
        ty: RustTyDecomposition<'vir>,
    },
    Mir {
        const_: mir::Const<'vir>,
        encoding_depth: usize, // current encoding depth
        def_id: DefId,         // DefId of the current function
        span: Span,
    },
}

/// Encodes constants into snapshot expressions. The evaluation of a constant
/// is assumed to be side-effect free, as enforced by the compiler. This encoder
/// handles two different kinds of constants: ones coming from the MIR and ones
/// coming from the type system.
///
/// See "Representing constants" in the rustc dev guide for an overview:
/// https://rustc-dev-guide.rust-lang.org/mir/index.html#representing-constants
pub struct ConstEnc;

thread_local! {
    /// Counter ensuring every emitted constant gets a unique Viper name.
    static CONST_CTR: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

struct Enc<'enc, 'vir: 'enc> {
    deps: &'enc mut TaskEncoderDependencies<'vir, ConstEnc>,
    ecx: &'enc InterpCx<'vir, CompileTimeMachine<'vir>>,
    span: Span,
    functions: Vec<vir::Function<'vir>>,
}

impl<'enc, 'vir: 'enc> Enc<'enc, 'vir> {
    /// Encodes the `(address, metadata, referent_snapshot)` triple of a
    /// reference constant. The reference's generic args are `[region, inner]`,
    /// so the referent type is at index 1; the pointer-metadata type is derived
    /// from the referent (`()` for sized referents, `usize` for slices/`str`).
    fn encode_ref_addr_snap(
        &mut self,
        val: impl Projectable<'vir, CtfeProvenance>,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<
        (
            vir::ExprRef<'vir>,
            vir::ExprCSnap<'vir>,
            vir::ExprSnap<'vir>,
        ),
        EncodeFullError<'vir, ConstEnc>,
    > {
        let ref_data = ty.ty.ref_data().unwrap();
        let inner_ty = ref_data.referent.decompose_normalize(ty.args);
        let metadata_ty = ref_data.metadata.decompose_normalize(ty.args);
        assert!(
            !metadata_ty.ty.specifics.is_param(),
            "expected const metadata type to be fully monomorphized"
        );

        let data = self.ecx.deref_pointer(&val).unwrap();
        let data_ptr = data.ptr();
        // Metadata
        let metadata = self.deps.require_dep::<TyUsePureEnc>(metadata_ty)?;
        let metadata = if data.meta().has_meta() {
            let meta = data.meta().unwrap_meta();
            ConstEnc::encode_scalar_ty(self.deps, meta, metadata_ty, metadata)?
        } else {
            metadata
                .zst_to_snap()
                .expect("pointer claims to have no metadata, so should be type `()`")
        };
        // Data
        let snap = self.encode_const_val_tree(data, inner_ty)?;
        // Address
        let rel_addr = match data_ptr.into_pointer_or_addr() {
            Ok(ptr) => {
                ((ptr.provenance.alloc_id().0.get() as u128) << 64)
                    | ptr.prov_and_relative_offset().1.bytes() as u128
            }
            Err(addr) => addr.bytes() as u128,
        };
        let addr_to_ref = self.deps.require_dep::<RefDataEnc>(())?.addr_to_ref;
        let addr = vir::with_vcx(|vcx| vcx.mk_const_expr(vir::ConstData::Int(rel_addr)));
        let addr = addr_to_ref(addr.downcast_ty());
        Ok((addr, metadata, snap.upcast_ty()))
    }

    fn encode_const_val_tree(
        &mut self,
        val: impl Projectable<'vir, CtfeProvenance>,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, ConstEnc>> {
        let ty_enc = self.deps.require_dep::<TyUsePureEnc>(ty)?;
        vir::with_vcx(|vcx| {
            Ok(match &ty_enc.specifics {
                super::ty::TySpecifics::ArrayLike(array_data) => {
                    let ty_array = ty.ty.expect_array();
                    let elem_ty = ty_array.data.decompose_normalize(ty.args);
                    let elem_len = val.len(self.ecx).unwrap();
                    let mut posts = Vec::new();
                    let result = vcx.mk_result(ty_enc.snapshot.downcast_ty());
                    for idx in 0..elem_len {
                        let snap = self.encode_const_val_tree(
                            self.ecx.project_index(&val, idx).unwrap(),
                            elem_ty,
                        )?;
                        let index = vcx
                            .mk_const_expr(vir::ConstData::Int(idx as u128))
                            .downcast_ty();
                        let index_ex = array_data.index(result, index);
                        posts.push(vcx.mk_eq_expr(snap.upcast_ty(), index_ex));
                    }
                    self.fresh_function(&posts, ty_enc.snapshot.downcast_ty())
                }
                super::ty::TySpecifics::Opaque(_) => {
                    self.fresh_function(&[], ty_enc.snapshot.downcast_ty())
                }
                super::ty::TySpecifics::Primitive(prim) => {
                    let int = self
                        .ecx
                        .read_scalar(&val)
                        .unwrap()
                        .try_to_scalar_int()
                        .expect("scalar should be an integer");
                    let val = int.to_bits(int.size());
                    let val = prim.expr_from_bits(*ty.ty.expect_primitive(), val);
                    (prim.prim_to_snap)(val)
                }
                super::ty::TySpecifics::ImmRef(immref) => {
                    let (addr, metadata, snap) = self.encode_ref_addr_snap(val, ty)?;
                    immref.prim_to_snap(addr, metadata.upcast_ty(), snap)
                }
                super::ty::TySpecifics::MutRef(mutref) => {
                    let (addr, metadata, snap) = self.encode_ref_addr_snap(val, ty)?;
                    mutref.prim_to_snap(addr, metadata.upcast_ty(), snap)
                }
                super::ty::TySpecifics::StructLike(struct_data) => {
                    let mut snaps = Vec::new();
                    for (idx, field) in ty.ty.expect_structlike().fields.iter().enumerate() {
                        snaps.push(
                            self.encode_const_val_tree(
                                self.ecx.project_field(&val, idx.into()).unwrap(),
                                field.decompose_normalize(ty.args),
                            )?
                            .upcast_ty(),
                        );
                    }
                    struct_data.field_snaps_to_snap(snaps)
                }
                super::ty::TySpecifics::EnumLike(enum_data) => {
                    let variant_idx = self.ecx.read_discriminant(&val).unwrap();
                    let mut snaps = Vec::new();
                    for (idx, field) in ty.ty.expect_enumlike().variants[variant_idx.as_usize()]
                        .inner
                        .fields
                        .iter()
                        .enumerate()
                    {
                        snaps.push(
                            self.encode_const_val_tree(
                                self.ecx.project_field(&val, idx.into()).unwrap(),
                                field.decompose_normalize(ty.args),
                            )?
                            .upcast_ty(),
                        );
                    }
                    enum_data.variants[variant_idx.as_usize()]
                        .inner
                        .field_snaps_to_snap(snaps)
                }
                _ => unreachable!(),
            })
        })
    }

    fn fresh_function<T: vir::CompType>(
        &mut self,
        posts: &[vir::ExprBool<'vir>],
        result_ty: vir::Type<'vir, T>,
    ) -> vir::Expr<'vir, T> {
        vir::with_vcx(|vcx| {
            let id = CONST_CTR.with(|c| {
                let v = c.get();
                c.set(v + 1);
                v
            });
            // `source_callsite()` walks out of any macro expansion to the user's call site.
            let span_pos = vcx
                .tcx()
                .sess
                .source_map()
                .lookup_char_pos(self.span.source_callsite().lo());
            let idn = vir::vir_format_identifier!(
                vcx,
                "const_{}_{}_{}",
                span_pos.line,
                span_pos.col_display,
                id,
            );
            let gen_snap_func_idn: FunctionIdn<'_, (), T> = FunctionIdn::new(idn, (), result_ty);
            self.functions.push(vcx.mk_function(
                gen_snap_func_idn,
                (),
                &[],
                vcx.alloc_slice(posts),
                None,
                None,
            ));
            (gen_snap_func_idn)()
        })
    }
}

impl ConstEnc {
    fn encode_ty_const<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        const_: ty::Const<'vir>,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, ConstEnc>> {
        match const_.kind() {
            ty::ConstKind::Param(param) => {
                let params = deps.require_dep::<GenericParamsEnc>(ty.args.context())?;
                Ok(params.const_expr(param))
            }
            ty::ConstKind::Value(val) => {
                let val = vir::with_vcx(|vcx| vcx.tcx().valtree_to_const_val(val));
                Self::encode_const_val_ty(deps, val, ty)
            }
            k => todo!("const kind {k:?}"),
        }
    }

    fn encode_const_val_ty<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: RustTyDecomposition<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, ConstEnc>> {
        let ty_enc = deps.require_dep::<TyUsePureEnc>(ty)?;
        Ok(match val {
            ConstValue::Scalar(s) => Self::encode_scalar_ty(deps, s, ty, ty_enc)?,
            ConstValue::ZeroSized => {
                let s = ty_enc.expect_structlike();
                s.field_snaps_to_snap(Vec::new())
            }
            // Encode `&str` constants to an opaque domain. If we ever want to perform string reasoning
            // we will need to revisit this encoding, but for the moment this allows assertions to avoid
            // crashing Prusti.
            ConstValue::Slice { meta, .. } => {
                let kind = ty
                    .ty
                    .ref_data()
                    .expect("slice constant should be a reference type");
                let metadata_ty = kind.metadata.decompose_normalize(ty.args);
                assert!(
                    metadata_ty.ty.expect_primitive().is_usize(),
                    "slice constant metadata should be a usize"
                );
                let ref_ty = ty_enc.expect_immref();

                let metadata = deps
                    .require_dep::<TyUsePureEnc>(metadata_ty)?
                    .expect_primitive();
                let inner_ty = kind.referent.decompose_normalize(ty.args);
                let inner = deps.require_dep::<TyUsePureEnc>(inner_ty)?;
                let TySpecifics::Opaque(inner) = &inner.specifics else {
                    todo!("ConstValue::Slice: {ty:?}");
                };
                // first, we create the metadata and string snapshots
                let meta =
                    metadata.expr_from_bits(*metadata_ty.ty.expect_primitive(), meta as u128);
                let meta = (metadata.prim_to_snap)(meta).upcast_ty();
                // TODO: this should use `fresh_function` instead to get a different value for different constants!
                let inner = (inner.arbitrary)().upcast_ty();
                // wrap it in a ref
                vir::with_vcx(|vcx| ref_ty.prim_to_snap(vcx.mk_null(), meta, inner))
            }
            ConstValue::Indirect { .. } => todo!("ConstValue::Indirect"),
        })
    }

    fn encode_scalar_ty<'vir>(
        _deps: &mut TaskEncoderDependencies<'vir, Self>,
        scalar: Scalar,
        ty: RustTyDecomposition<'vir>,
        ty_enc: TyUsePure<'vir>,
    ) -> Result<vir::ExprCSnap<'vir>, EncodeFullError<'vir, ConstEnc>> {
        Ok(match scalar {
            Scalar::Int(int) => {
                let prim = ty_enc.expect_primitive();
                let val = int.to_bits(int.size());
                let val = prim.expr_from_bits(*ty.ty.expect_primitive(), val);
                (prim.prim_to_snap)(val)
            }
            Scalar::Ptr(ptr, _) => {
                match vir::with_vcx(|vcx| vcx.tcx().global_alloc(ptr.provenance.alloc_id())) {
                    GlobalAlloc::Memory(_mem) => unreachable!(),
                    _ => todo!(),
                }
            }
        })
    }

    fn encode_const_val<'vir>(
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        val: ConstValue,
        ty: ty::Ty<'vir>,
        context: GParams<'vir>,
        span: Span,
    ) -> EncodeFullResult<'vir, Self> {
        let ty_ctxt_at = vir::with_vcx(|vcx| vcx.tcx().at(span));
        let (ecx, valtree) =
            mk_eval_cx_for_const_val(ty_ctxt_at, TypingEnv::fully_monomorphized(), val, ty)
                .unwrap();
        let mut enc = Enc {
            ecx: &ecx,
            deps,
            span,
            functions: Vec::new(),
        };
        let ty = RustTyDecomposition::from_ty(ty, context);
        let expr = enc.encode_const_val_tree(valtree, ty)?;
        Ok((enc.functions, expr))
    }
}

impl TaskEncoder for ConstEnc {
    task_encoder::encoder_cache!(ConstEnc);
    const ENCODER_NAME: &'static str = "const encoder";

    type TaskDescription<'vir> = ConstEncTask<'vir>;
    type OutputFullDependency<'vir> = vir::ExprCSnap<'vir>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;
    type EncodingError = ();

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for output in Self::all_outputs_local_no_errors(program) {
            for fun in output {
                program.add_function(fun);
            }
        }
        // reset the counter across compilations
        CONST_CTR.with(|c| {
            let v = c.get();
            c.set(v + 1);
        });
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        Ok(match *task_key {
            ConstEncTask::Ty { const_, ty } => {
                (Vec::new(), Self::encode_ty_const(deps, const_, ty)?)
            }
            ConstEncTask::Mir {
                const_,
                encoding_depth,
                def_id,
                span,
            } => match const_ {
                mir::Const::Val(val, ty) => {
                    Self::encode_const_val(deps, val, ty, def_id.into(), span)?
                }
                mir::Const::Unevaluated(uneval, ty) => vir::with_vcx(|vcx| {
                    let resolved = {
                        let typing_env = ty::TypingEnv::post_analysis(vcx.tcx(), def_id);
                        vcx.tcx()
                            .const_eval_resolve(typing_env, uneval, vcx.tcx().def_span(def_id))
                    };
                    if let Ok(val) = resolved {
                        Self::encode_const_val(deps, val, ty, def_id.into(), span)
                    } else if let Some(promoted) = uneval.promoted {
                        let task = MirPureEncTask {
                            encoding_depth: encoding_depth + 1,
                            parent_def_id: uneval.def,
                            param_env: vcx.tcx().param_env(uneval.def),
                            substs: ty::List::identity_for_item(vcx.tcx(), uneval.def),
                            kind: PureKind::Constant(promoted),
                            caller_def_id: Some(def_id),
                        };
                        let expr = deps.require_dep::<MirPureEnc>(task)?.expr;
                        use vir::Reify;
                        let args = Default::default();
                        Ok((
                            Vec::new(),
                            expr.reify(vcx, (uneval.def, vcx.alloc(args))).downcast_ty(),
                        ))
                    } else {
                        todo!("const too generic")
                    }
                })?,
                mir::Const::Ty(ty, const_) => {
                    let ty = RustTyDecomposition::from_ty(ty, def_id);
                    (Vec::new(), Self::encode_ty_const(deps, const_, ty)?)
                }
            },
        })
    }
}
