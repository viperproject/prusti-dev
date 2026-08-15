use prusti_interface::{PrustiError, environment::EnvQuery};
use prusti_rustc_interface::{
    abi,
    middle::ty,
    span::{Span, Symbol, def_id::DefId},
};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, FunctionIdn};

use crate::encoders::ty::{
    RustTyDecomposition,
    generics::GArgs,
    interpretation::float::FloatDomain,
    use_pure::{TyUsePure, TyUsePureEnc, TyUsePureImmRef},
};

/// Marker for the "mode" spec builtins (`old`/`rel`/`before_expiry`).
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum Mode {
    Old,
    Rel(usize),
    BeforeExpiry,
}

/// The pure-only spec builtins (quantifiers, spec blocks, mode markers),
/// handled directly by the pure encoder rather than [`PrustiBuiltinEnc`].
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum SpecBuiltin {
    Forall,
    Exists,
    SpecBlock,
    ModeStart(Mode),
    ModeEnd(Mode),
}

/// The operations of the `Ghost` wrapper.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum GhostOp {
    New,
    Deref,
    /// `ghost_call(&closure, body)`, the `ghost!` block marker: the block's
    /// value is `body` (evaluated inline in the block's dead arm, which the
    /// encoders jump into; see `ghost_switches` in `SpecBlocks`), wrapped in
    /// `Ghost`. The never-called closure operand only exists for the
    /// compiler to check the body against `Fn` capture rules.
    Call,
    /// `ghost_erased()`, the runtime stand-in arm of a `ghost!` block; the
    /// encoders skip it, so this is only reached by stray direct calls.
    Erased,
}

/// The operations of the `Seq` builtin.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum SeqOp {
    Empty,
    Single,
    Append,
    Update,
    Contains,
    /// `Index<Int>` (an element, as a `Ghost`) or `Index<Range*<Int>>` (a
    /// subsequence); disambiguated by the index type.
    Index,
    Len,
}

/// An operation shared by the `Set` and `Multiset` builtins. `Contains` is
/// a `bool` for sets and the multiplicity (an `Int`) for multisets.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum AnySetOp {
    Empty,
    Single,
    Union,
    Intersection,
    Difference,
    IsSubset,
    Contains,
    Len,
}

/// The operations of the `Map` builtin.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum MapOp {
    Empty,
    Insert,
    Len,
    Keys,
    Values,
    Setminus,
    Contains,
    Index,
}

/// An operation shared by the numeric builtins (`Int`/`Real`); `Rem` exists
/// only on `Int`.
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum NumOp {
    From,
    Add,
    Sub,
    Mul,
    Div,
    Rem,
    Neg,
    Lt,
    Le,
    Gt,
    Ge,
    Cmp,
    PartialCmp,
    Max,
    Min,
    Clamp,
}

/// The float classification/manipulation builtins (the free functions
/// `f{16,32,64,128}_{is_nan,is_infinite,abs}`).
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum FloatOp {
    IsNan,
    IsInfinite,
    Abs,
}

/// A `prusti_contracts` builtin, classified from the callee and grouped by
/// the ghost type it belongs to. All groups except [`PrustiBuiltin::Spec`]
/// are operand-based and encoded by [`PrustiBuiltinEnc`].
#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub enum PrustiBuiltin {
    Spec(SpecBuiltin),
    Ghost(GhostOp),
    /// The `PartialEq` methods on the ghost types: snapshot equality behind
    /// the `&self`/`&other` receivers.
    SnapEq,
    SnapNe,
    SnapClone,
    Seq(SeqOp),
    /// An operation on `Set` (`multiset: false`) or `Multiset` (`true`).
    AnySet {
        multiset: bool,
        op: AnySetOp,
    },
    Map(MapOp),
    Int(NumOp),
    Real(NumOp),
    Float(FloatOp, ty::FloatTy),
}

impl PrustiBuiltin {
    /// Classifies the call to `def_id`. Returns `None` iff the called function
    /// does not belong to the `prusti_contracts` crate (a trait method call is
    /// attributed to the crate of the `impl` it relies on, e.g. `PartialOrd::le`
    /// on `Int` belongs to `prusti_contracts` even though the default `le` body
    /// lives in `core`), or is one of the crate's few ordinary functions with
    /// a meaningful body (encoded as a normal call).
    pub fn new(def_id: DefId, args: GArgs<'_>) -> Option<Self> {
        vir::with_vcx(|vcx| {
            let tcx = vcx.tcx();
            let env_query = EnvQuery::new(tcx);
            // The trait impl the call relies on (if any), used both to
            // attribute the call to a crate and to name the impl's self type.
            let impl_def_id = env_query.find_trait_impl_of_method_call(
                args.context().typing_env(),
                def_id,
                tcx.mk_args(args.args()),
            );
            if tcx.crate_name(impl_def_id.unwrap_or(def_id).krate).as_str() != "prusti_contracts" {
                return None;
            }

            let item_name = tcx.item_name(def_id);
            let item = item_name.as_str();
            // The self type of the impl the call relies on: the selected
            // trait impl for trait method calls (whether or not it overrides
            // the method), or the enclosing inherent impl otherwise. Matched
            // by its plain ADT name (as in `RustTySpecifics::from_adt`),
            // which is stable under type-parameter renames and rustc's type
            // formatting.
            let self_ty_name =
                impl_def_id
                    .or_else(|| tcx.impl_of_assoc(def_id))
                    .and_then(|impl_def_id| {
                        Self::prusti_adt_name(tcx, tcx.type_of(impl_def_id).instantiate_identity())
                    });
            let self_ty_name = self_ty_name.as_ref().map(|name| name.as_str());
            let rel_index = || {
                args.args()[0]
                    .expect_const()
                    .to_value()
                    .valtree
                    .try_to_scalar_int()
                    .unwrap()
                    .to_target_usize(tcx) as usize
            };
            // The methods defined on all ghost types, early return here.
            match (self_ty_name, item) {
                (Some(_), "eq") => return Some(Self::SnapEq),
                (Some(_), "ne") => return Some(Self::SnapNe),
                (Some(_), "clone") => return Some(Self::SnapClone),
                (Some(_), "clone_from") => return None,
                _ => (),
            };
            Some(match self_ty_name {
                None => match item {
                    // TODO: how to handle this function?
                    "prusti_terminates_trusted" => return None,
                    "forall" => Self::Spec(SpecBuiltin::Forall),
                    "exists" => Self::Spec(SpecBuiltin::Exists),
                    "spec_block" => Self::Spec(SpecBuiltin::SpecBlock),
                    "ghost_call" => Self::Ghost(GhostOp::Call),
                    "ghost_erased" => Self::Ghost(GhostOp::Erased),
                    "old_start" => Self::Spec(SpecBuiltin::ModeStart(Mode::Old)),
                    "old_end" => Self::Spec(SpecBuiltin::ModeEnd(Mode::Old)),
                    "rel_start" => Self::Spec(SpecBuiltin::ModeStart(Mode::Rel(rel_index()))),
                    "rel_end" => Self::Spec(SpecBuiltin::ModeEnd(Mode::Rel(rel_index()))),
                    "before_expiry_start" => Self::Spec(SpecBuiltin::ModeStart(Mode::BeforeExpiry)),
                    "before_expiry_end" => Self::Spec(SpecBuiltin::ModeEnd(Mode::BeforeExpiry)),
                    other => Self::float_fn(other).unwrap_or_else(|| {
                        todo!("unsupported `prusti_contracts` function {other}")
                    }),
                },
                Some("Ghost") => match item {
                    "new" | "new_ref" => Self::Ghost(GhostOp::New),
                    "deref" => Self::Ghost(GhostOp::Deref),
                    other => todo!("unsupported `Ghost` function {other}"),
                },
                Some("Seq") => match item {
                    "new" => Self::Seq(SeqOp::Empty),
                    "single" | "single_ref" => Self::Seq(SeqOp::Single),
                    "append" => Self::Seq(SeqOp::Append),
                    "update" => Self::Seq(SeqOp::Update),
                    "contains" => Self::Seq(SeqOp::Contains),
                    "index" => Self::Seq(SeqOp::Index),
                    "len" => Self::Seq(SeqOp::Len),
                    other => todo!("unsupported `Seq` function {other}"),
                },
                Some(name @ ("Set" | "Multiset")) => {
                    let multiset = name == "Multiset";
                    Self::AnySet {
                        multiset,
                        op: match item {
                            "new" => AnySetOp::Empty,
                            "single" | "single_ref" => AnySetOp::Single,
                            "union" => AnySetOp::Union,
                            "intersection" => AnySetOp::Intersection,
                            "difference" => AnySetOp::Difference,
                            "is_subset" => AnySetOp::IsSubset,
                            "contains" => AnySetOp::Contains,
                            "len" => AnySetOp::Len,
                            other => todo!("unsupported set function {other}"),
                        },
                    }
                }
                Some("Map") => match item {
                    "new" => Self::Map(MapOp::Empty),
                    "insert" => Self::Map(MapOp::Insert),
                    "len" => Self::Map(MapOp::Len),
                    "keys" => Self::Map(MapOp::Keys),
                    "values" => Self::Map(MapOp::Values),
                    "setminus" => Self::Map(MapOp::Setminus),
                    "contains" => Self::Map(MapOp::Contains),
                    "index" => Self::Map(MapOp::Index),
                    other => todo!("unsupported `Map` function {other}"),
                },
                Some("Int") => Self::Int(Self::num_op(item)),
                Some("Real") => Self::Real(Self::num_op(item)),
                Some(other) => todo!("unsupported `prusti_contracts` function {other}::{item}"),
            })
        })
    }

    /// Returns `true` if the function is not encodable in impure (e.g. mode change)
    /// or if it could affect control flow (e.g. `bool` returning functions).
    /// These are forbidden in impure code, and should return an error.
    pub fn is_spec_only(&self) -> bool {
        match self {
            Self::Spec(_) | Self::SnapEq | Self::SnapNe => true,
            // `Call`/`Erased` are legitimate only inside a `ghost!` block's
            // dead arm, which is exempt from the spec-only rejection: a stray
            // executable `ghost_call` (i.e. not from a `ghost!` block) would
            // verify code whose runtime body is `unreachable!()`.
            Self::Ghost(GhostOp::Deref | GhostOp::Call | GhostOp::Erased) => true,
            Self::Seq(SeqOp::Contains) => true,
            Self::AnySet {
                op: AnySetOp::IsSubset,
                ..
            } => true,
            // `Multiset::contains` (the multiplicity) is a shared operation.
            Self::AnySet {
                multiset: false,
                op: AnySetOp::Contains,
            } => true,
            Self::Map(MapOp::Contains) => true,
            Self::Int(op) | Self::Real(op) => matches!(
                op,
                NumOp::Lt | NumOp::Le | NumOp::Gt | NumOp::Ge | NumOp::Cmp | NumOp::PartialCmp
            ),
            _ => false,
        }
    }

    /// The float classification/manipulation free functions
    /// (`f{16,32,64,128}_{is_nan,is_infinite,abs}`).
    fn float_fn(name: &str) -> Option<Self> {
        let (width, op) = name.split_once('_')?;
        let fl = match width {
            "f16" => ty::FloatTy::F16,
            "f32" => ty::FloatTy::F32,
            "f64" => ty::FloatTy::F64,
            "f128" => ty::FloatTy::F128,
            _ => return None,
        };
        let op = match op {
            "is_nan" => FloatOp::IsNan,
            "is_infinite" => FloatOp::IsInfinite,
            "abs" => FloatOp::Abs,
            _ => return None,
        };
        Some(Self::Float(op, fl))
    }

    /// The shared `Int`/`Real` method names.
    fn num_op(name: &str) -> NumOp {
        match name {
            "from" => NumOp::From,
            "add" => NumOp::Add,
            "sub" => NumOp::Sub,
            "mul" => NumOp::Mul,
            "div" => NumOp::Div,
            "rem" => NumOp::Rem,
            "neg" => NumOp::Neg,
            "lt" => NumOp::Lt,
            "le" => NumOp::Le,
            "gt" => NumOp::Gt,
            "ge" => NumOp::Ge,
            "cmp" => NumOp::Cmp,
            "partial_cmp" => NumOp::PartialCmp,
            "max" => NumOp::Max,
            "min" => NumOp::Min,
            "clamp" => NumOp::Clamp,
            other => todo!("unsupported numeric function {other}"),
        }
    }

    /// Returns the ADT name of a `prusti_contracts` type, if `ty` is an
    /// ADT from the `prusti_contracts` crate.
    fn prusti_adt_name<'tcx>(tcx: ty::TyCtxt<'tcx>, ty: ty::Ty<'tcx>) -> Option<Symbol> {
        match ty.kind() {
            ty::TyKind::Adt(adt, _)
                if EnvQuery::new(tcx).is_adt_in_crate(*adt, "prusti_contracts") =>
            {
                Some(adt.non_enum_variant().name)
            }
            _ => None,
        }
    }
}

/// Encodes the operand-based `prusti_contracts` builtins (`Int`/`Real`
/// arithmetic and comparisons, the float classification functions, and the
/// ghost collection operations) as snapshot expressions with one hole per
/// operand.
/// The holes are filled by `reify`ing the expression with the operand
/// snapshots encoded by the caller, so the same (cached) output serves both
/// the pure and the impure encoder.
pub struct PrustiBuiltinEnc;

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct PrustiBuiltinTask<'vir> {
    pub builtin: PrustiBuiltin,
    pub def_id: DefId,
    pub args: GArgs<'vir>,
    /// Whether the call site is in pure code. The partial collection
    /// operations (element indexing/update/lookup) encode to their *checked*
    /// native form in impure code (where the well-definedness obligation is
    /// a meaningful verification condition), and to the total wrappers of
    /// [`CollectionOpsEnc`] in pure code (where the precondition-free `f_`
    /// functions could never discharge it).
    pub is_pure: bool,
    /// The call-site span (`is_none()` iff `is_pure`). The returned expression
    /// is partial iff `!is_pure`, therefore in this case we need to report
    /// verification errors with this span (thus each impure call site is
    /// encoded separately).
    pub span: Option<Span>,
}

/// The operand snapshots filling the holes of a [`PrustiBuiltinExpr`].
type PrustiBuiltinOperands<'vir> = &'vir [vir::ExprSnap<'vir>];

/// A snapshot expression with one hole (`Lazy` node) per operand; the holes
/// are filled with [`PrustiBuiltinExpr::apply`].
#[derive(Clone, Copy, Debug)]
pub struct PrustiBuiltinExpr<'vir>(
    vir::ExprGenSnap<'vir, PrustiBuiltinOperands<'vir>, vir::ExprKind<'vir>>,
);

impl<'vir> PrustiBuiltinExpr<'vir> {
    /// Fills the operand holes with `operands`, in the caller's
    /// `Curr`/`Next` expression domain.
    pub fn apply<Curr: 'vir, Next: 'vir>(
        self,
        vcx: &'vir vir::VirCtxt<'vir>,
        operands: &[vir::ExprGenSnap<'vir, Curr, Next>],
    ) -> vir::ExprGenSnap<'vir, Curr, Next> {
        // SAFETY: reinterpret the kind of the operand holes (and thus of the
        // expression itself) from hole-free operands to operands in the
        // caller's domain: the `Lazy` operand holes only index into the
        // operand slice and splice the operand's `kind` verbatim, so they are
        // oblivious to any holes the operands themselves may carry.
        let expr = unsafe {
            std::mem::transmute::<
                vir::ExprGen<'vir, &'vir [vir::ExprSnap<'vir>], vir::ExprKind<'vir>, vir::Snap>,
                vir::ExprGen<
                    'vir,
                    &'vir [vir::ExprGenSnap<'vir, Curr, Next>],
                    vir::ExprKindGen<'vir, Curr, Next>,
                    vir::Snap,
                >,
            >(self.0)
        };
        use vir::Reify;
        expr.reify(vcx, vcx.alloc_slice(operands))
    }
}

type ExprRet<'vir, T> = vir::ExprGen<'vir, PrustiBuiltinOperands<'vir>, vir::ExprKind<'vir>, T>;

type EncResult<'vir, T> = Result<T, EncodeFullError<'vir, PrustiBuiltinEnc>>;

impl TaskEncoder for PrustiBuiltinEnc {
    task_encoder::encoder_cache!(PrustiBuiltinEnc);
    const ENCODER_NAME: &'static str = "prusti builtin encoder";

    type TaskDescription<'vir> = PrustiBuiltinTask<'vir>;

    type OutputFullDependency<'vir> = PrustiBuiltinExpr<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        // The span of a checked operation is part of the key, so this
        // encoding belongs to (and is reachable from) that call statement.
        vir::with_vcx(|vcx| match task_key.span {
            Some(span) => vcx.with_span(span, |vcx| Self::encode(task_key, deps, vcx)),
            None => Self::encode(task_key, deps, vcx),
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        CollectionOpsEnc::emit_outputs(program);
    }
}

impl PrustiBuiltinEnc {
    /// Encodes the operation of `task_key`, with its span (if it is a
    /// checked operation) on the span stack.
    fn encode<'vir>(
        task_key: &PrustiBuiltinTask<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
        vcx: &'vir vir::VirCtxt<'vir>,
    ) -> EncodeFullResult<'vir, Self> {
        let PrustiBuiltinTask {
            builtin,
            def_id,
            args,
            is_pure,
            span,
        } = *task_key;
        assert_eq!(is_pure, span.is_none());
        let tcx = vcx.tcx();
        let sig = tcx
            .fn_sig(def_id)
            .instantiate(tcx, args.args())
            .skip_binder();

        // One hole per operand, typed with the operand's snapshot type.
        let operands = (0..sig.inputs().len())
            .map(|i| {
                let ty = RustTyDecomposition::from_ty(sig.inputs()[i], args.context());
                let snap_ty = deps.require_ref::<TyUsePureEnc>(ty)?.snapshot;
                Ok(vcx.mk_lazy_expr(
                    vir::vir_format!(vcx, "prusti_builtin_operand_{i}"),
                    snap_ty,
                    Box::new(move |_vcx, lctx: PrustiBuiltinOperands<'vir>| {
                        assert_eq!(lctx.len(), sig.inputs().len());
                        lctx[i].kind
                    }),
                ))
            })
            .collect::<EncResult<'vir, Vec<ExprRet<'vir, vir::Snap>>>>()?;
        let operands = &operands;

        let mut ctxt = BuiltinCtxt {
            vcx,
            deps,
            sig,
            args,
            operands,
            span,
        };
        let res: ExprRet<'vir, vir::Snap> = match builtin {
            PrustiBuiltin::Spec(_) => {
                unreachable!("pure-only builtin in `PrustiBuiltinEnc`: {builtin:?}")
            }
            PrustiBuiltin::Ghost(op) => ctxt.encode_ghost(op)?,
            PrustiBuiltin::SnapEq | PrustiBuiltin::SnapNe => {
                let bin_op = match builtin {
                    PrustiBuiltin::SnapEq => vir::BinOpKind::CmpEq,
                    PrustiBuiltin::SnapNe => vir::BinOpKind::CmpNe,
                    _ => unreachable!(),
                };
                let (lhs, rhs) = ctxt.deref_operands::<vir::Snap>()?;
                ctxt.native_cmp(bin_op, lhs, rhs).upcast_ty()
            }
            PrustiBuiltin::SnapClone => ctxt.deref_operand(0)?,
            PrustiBuiltin::Seq(op) => ctxt.encode_seq(op)?,
            PrustiBuiltin::AnySet { multiset, op } => ctxt.encode_any_set(multiset, op)?,
            PrustiBuiltin::Map(op) => ctxt.encode_map(op)?,
            // `From` differs structurally between the numeric types; the
            // shared operations are handled by `encode_num`.
            PrustiBuiltin::Int(NumOp::From) => {
                let prim = *ctxt.e_input(0)?.expect_primitive();
                let val = prim.snap_to_prim(ctxt.operands[0].downcast_ty());
                val.downcast_ty::<vir::Int>().upcast_ty()
            }
            PrustiBuiltin::Int(op) => ctxt.encode_num::<vir::Int>(op, false)?,
            PrustiBuiltin::Real(NumOp::From) => {
                let fp_to_real = ctxt.e_input(0)?.expect_float().fp_to_real;
                fp_to_real.call()(ctxt.operands[0].downcast_ty()).upcast_ty()
            }
            PrustiBuiltin::Real(op) => ctxt.encode_num::<vir::Perm>(op, true)?,
            PrustiBuiltin::Float(op, fl) => {
                let domain = ctxt.float_domain(fl)?;
                let operand = ctxt.operands[0].downcast_ty();
                match op {
                    FloatOp::IsNan => domain.fp_is_nan.call()(operand).upcast_ty(),
                    FloatOp::IsInfinite => domain.fp_is_infinite.call()(operand).upcast_ty(),
                    FloatOp::Abs => domain.fp_abs.call()(operand).upcast_ty(),
                }
            }
        };
        Ok(((), PrustiBuiltinExpr(res)))
    }
}

/// The per-task encoding context of [`PrustiBuiltinEnc`]: the values every
/// group encoder and helper needs, so they are not threaded through each
/// signature.
struct BuiltinCtxt<'enc, 'vir> {
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &'enc mut TaskEncoderDependencies<'vir, PrustiBuiltinEnc>,
    sig: ty::FnSig<'vir>,
    args: GArgs<'vir>,
    operands: &'enc [ExprRet<'vir, vir::Snap>],
    span: Option<Span>,
}

impl<'enc, 'vir> BuiltinCtxt<'enc, 'vir> {
    /// Encodes a `Ghost` operation.
    fn encode_ghost(&mut self, op: GhostOp) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        Ok(match op {
            GhostOp::New => {
                let expected = Self::adt_type_arg(self.sig.output(), 0);
                let value = self.value_operand(0, expected)?;
                self.e_output()?
                    .expect_structlike()
                    .field_snaps_to_snap(vec![value])
                    .upcast_ty()
            }
            GhostOp::Deref => {
                let ghost = self.e_input_deref(0)?.expect_structlike();
                let ghost_snap = self.deref_operand(0)?;
                let value = ghost.fields[0].read(ghost_snap);
                self.wrap_in_immref(value)?
            }
            // The block's value is the inline body operand; the checker
            // closure operand is ignored.
            GhostOp::Call => self
                .e_output()?
                .expect_structlike()
                .field_snaps_to_snap(vec![self.operands[1]])
                .upcast_ty(),
            GhostOp::Erased => {
                return Err(EncodeFullError::DependencyError(vec![(
                    PrustiBuiltinEnc::ENCODER_NAME,
                    "`ghost_erased` outside of a `ghost!` block".to_string(),
                    self.span.into_iter().collect(),
                )]));
            }
        })
    }

    /// Encodes a `Seq` operation.
    fn encode_seq(&mut self, op: SeqOp) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        Ok(match op {
            SeqOp::Empty => self
                .vcx
                .mk_seq_literal_expr::<_, _, vir::PSnap>(&[], vir::TYPE_PSNAP)
                .upcast_ty(),
            SeqOp::Single => {
                let seq = *self.e_output()?.expect_builtin();
                let value = self.value_operand(0, Self::adt_type_arg(self.sig.output(), 0))?;
                let elem = seq.elem_caster().cast_to_callee_ctx(value);
                let elems = self.vcx.alloc_slice(&[elem.downcast_ty::<vir::PSnap>()]);
                self.vcx
                    .mk_seq_literal_expr(elems, vir::TYPE_PSNAP)
                    .upcast_ty()
            }
            SeqOp::Append => self
                .vcx
                .mk_seq_concat_expr(
                    self.operands[0].downcast_ty(),
                    self.operands[1].downcast_ty(),
                )
                .upcast_ty(),
            SeqOp::Update => {
                let seq = *self.e_input(0)?.expect_builtin();
                let idx = self.index_to_int(self.operands[1], self.sig.inputs()[1])?;
                let value = self.value_operand(2, Self::adt_type_arg(self.sig.inputs()[0], 0))?;
                let val = seq.elem_caster().cast_to_callee_ctx(value);
                if let Some(span) = self.span {
                    self.handle_partial_op_error(
                        "call.failed:seq.index.length",
                        "the update index may be out of bounds",
                        span,
                    );
                    self.handle_partial_op_error(
                        "call.failed:seq.index.negative",
                        "the update index may be negative",
                        span,
                    );
                    self.vcx
                        .mk_seq_update_expr(
                            self.operands[0].downcast_ty(),
                            idx,
                            val.downcast_ty::<vir::PSnap>(),
                        )
                        .upcast_ty()
                } else {
                    let seq_update = self
                        .deps
                        .require_ref::<CollectionOpsEnc>(CollectionOp::SeqUpdate)?
                        .expect_seq_update();
                    seq_update.call()(self.operands[0].downcast_ty(), idx, val.downcast_ty())
                        .upcast_ty()
                }
            }
            SeqOp::Contains => {
                let seq = *self.e_input(0)?.expect_builtin();
                let elem = self.value_operand(1, Self::adt_type_arg(self.sig.inputs()[0], 0))?;
                let elem = seq.elem_caster().cast_to_callee_ctx(elem);
                self.vcx
                    .mk_seq_contains_expr(
                        elem.downcast_ty::<vir::PSnap>(),
                        self.operands[0].downcast_ty(),
                    )
                    .upcast_ty()
            }
            SeqOp::Len => self
                .vcx
                .mk_collection_len_expr(self.operands[0].downcast_ty::<vir::Seq>())
                .upcast_ty(),
            SeqOp::Index => {
                let seq_data = *self.e_input_deref(0)?.expect_builtin();
                let seq = self.deref_operand(0)?;
                let lang = self.vcx.tcx().lang_items();
                // The index is `I` or `Range*<I>`, with `Int: From<I>`: `I`
                // is `Int` itself or a Rust integer (see `index_to_int`).
                let (index_adt, index_int_ty) = match self.sig.inputs()[1].kind() {
                    ty::TyKind::Adt(adt, adt_args) => (Some(adt.did()), adt_args.types().next()),
                    _ => (None, None),
                };
                // Slices in specs are total (the native clamping take/drop);
                // in impure code the bounds are *checked* via the
                // `prusti_seq_slice` precondition, matching Rust's panicking
                // slice semantics.

                let value = if index_adt.is_some() && index_adt == lang.range_struct() {
                    // `s[a..b]`
                    let int_ty = index_int_ty.unwrap();
                    let range = self.e_input(1)?.expect_structlike();
                    let range_snap = self.operands[1].downcast_ty::<vir::CSnap>();
                    let start = range.fields[0].read(range_snap);
                    let end = range.fields[1].read(range_snap);
                    let start = self.index_to_int(start, int_ty)?;
                    let end = self.index_to_int(end, int_ty)?;
                    self.seq_slice(seq, Some(start), Some(end))?
                } else if index_adt.is_some() && index_adt == lang.range_from_struct() {
                    // `s[a..]`
                    let int_ty = index_int_ty.unwrap();
                    let range = self.e_input(1)?.expect_structlike();
                    let start = range.fields[0].read(self.operands[1].downcast_ty());
                    let start = self.index_to_int(start, int_ty)?;
                    self.seq_slice(seq, Some(start), None)?
                } else if index_adt.is_some() && index_adt == lang.range_to_struct() {
                    // `s[..b]`
                    let int_ty = index_int_ty.unwrap();
                    let range = self.e_input(1)?.expect_structlike();
                    let end = range.fields[0].read(self.operands[1].downcast_ty());
                    let end = self.index_to_int(end, int_ty)?;
                    self.seq_slice(seq, None, Some(end))?
                } else {
                    // `s[i]`: the element, wrapped in the (single-field)
                    // `Ghost` struct of the output.
                    let idx = self.index_to_int(self.operands[1], self.sig.inputs()[1])?;
                    let elem = if let Some(span) = self.span {
                        self.handle_partial_op_error(
                            "call.failed:seq.index.length",
                            "the sequence index may be out of bounds",
                            span,
                        );
                        self.handle_partial_op_error(
                            "call.failed:seq.index.negative",
                            "the sequence index may be negative",
                            span,
                        );
                        self.vcx
                            .mk_seq_index_expr(seq, idx)
                            .downcast_ty::<vir::PSnap>()
                            .upcast_ty()
                    } else {
                        let seq_lookup = self
                            .deps
                            .require_ref::<CollectionOpsEnc>(CollectionOp::SeqLookup)?
                            .expect_seq_lookup();
                        seq_lookup.call()(seq, idx).upcast_ty()
                    };
                    let elem = seq_data.elem_caster().cast_to_caller_ctx(elem);
                    self.e_output_deref()?
                        .expect_structlike()
                        .field_snaps_to_snap(vec![elem])
                        .upcast_ty()
                };
                self.wrap_in_immref(value)?
            }
        })
    }

    /// A subsequence `seq[start..end]`; a `None` bound is the corresponding
    /// end of the sequence. Slices in specs are total (the native clamping
    /// take/drop); in impure code the bounds are *checked* via the
    /// `prusti_seq_slice_to`/`prusti_seq_slice_from` preconditions, matching
    /// Rust's panicking slice semantics. Either way, only the given bounds
    /// apply their operation.
    fn seq_slice(
        &mut self,
        seq: ExprRet<'vir, vir::Seq>,
        start: Option<ExprRet<'vir, vir::Int>>,
        end: Option<ExprRet<'vir, vir::Int>>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        Ok(if let Some(span) = self.span {
            self.handle_partial_op_error(
                "application.precondition:assertion.false",
                "the range bounds may be out of bounds",
                span,
            );
            // A two-sided `s[a..b]` composes the checked slices: the inner
            // `prusti_seq_slice_to` ensures `0 <= b <= |s|` and the outer
            // `prusti_seq_slice_from` then ensures `0 <= a <= b`, together
            // matching Rust's panicking condition.
            let seq = match end {
                Some(end) => {
                    let seq_slice_to = self
                        .deps
                        .require_ref::<CollectionOpsEnc>(CollectionOp::SeqSliceTo)?
                        .expect_seq_slice_to();
                    seq_slice_to.call()(seq, end)
                }
                None => seq,
            };
            let seq = match start {
                Some(start) => {
                    let seq_slice_from = self
                        .deps
                        .require_ref::<CollectionOpsEnc>(CollectionOp::SeqSliceFrom)?
                        .expect_seq_slice_from();
                    seq_slice_from.call()(seq, start)
                }
                None => seq,
            };
            seq.upcast_ty()
        } else {
            let seq = end.map_or(seq, |end| self.vcx.mk_seq_take_expr(seq, end));
            let seq = start.map_or(seq, |start| self.vcx.mk_seq_drop_expr(seq, start));
            seq.upcast_ty()
        })
    }

    /// Encodes a `Set`/`Multiset` operation; the two share every operation
    /// except the literal type and the `contains` result (`bool` vs the
    /// multiplicity).
    fn encode_any_set(
        &mut self,
        multiset: bool,
        op: AnySetOp,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        Ok(match op {
            AnySetOp::Empty | AnySetOp::Single => {
                let elems = if op == AnySetOp::Single {
                    let data = *self.e_output()?.expect_builtin();
                    let value = self.value_operand(0, Self::adt_type_arg(self.sig.output(), 0))?;
                    let elem = data.elem_caster().cast_to_callee_ctx(value);
                    self.vcx.alloc_slice(&[elem.downcast_ty::<vir::PSnap>()])
                } else {
                    &[]
                };
                if multiset {
                    self.vcx
                        .mk_multiset_literal_expr(elems, vir::TYPE_PSNAP)
                        .upcast_ty()
                } else {
                    self.vcx
                        .mk_set_literal_expr(elems, vir::TYPE_PSNAP)
                        .upcast_ty()
                }
            }
            AnySetOp::Union | AnySetOp::Intersection | AnySetOp::Difference => {
                let kind = match op {
                    AnySetOp::Union => vir::CollectionBinOpKind::Union,
                    AnySetOp::Intersection => vir::CollectionBinOpKind::Intersection,
                    AnySetOp::Difference => vir::CollectionBinOpKind::Difference,
                    _ => unreachable!(),
                };
                self.vcx
                    .mk_anyset_op_expr(kind, self.operands[0], self.operands[1])
                    .downcast_ty()
            }
            AnySetOp::IsSubset => self
                .vcx
                .mk_set_subset_expr(self.operands[0], self.operands[1])
                .upcast_ty(),
            AnySetOp::Contains => {
                let data = *self.e_input(0)?.expect_builtin();
                let elem = self.value_operand(1, Self::adt_type_arg(self.sig.inputs()[0], 0))?;
                let elem = data.elem_caster().cast_to_callee_ctx(elem);
                let elem = elem.downcast_ty::<vir::PSnap>();
                if multiset {
                    self.vcx
                        .mk_multiset_count_expr(elem, self.operands[0].downcast_ty())
                        .upcast_ty()
                } else {
                    self.vcx
                        .mk_set_in_expr(elem, self.operands[0].downcast_ty())
                        .upcast_ty()
                }
            }
            AnySetOp::Len => {
                if multiset {
                    self.vcx
                        .mk_collection_len_expr(self.operands[0].downcast_ty::<vir::Multiset>())
                        .upcast_ty()
                } else {
                    self.vcx
                        .mk_collection_len_expr(self.operands[0].downcast_ty::<vir::Set>())
                        .upcast_ty()
                }
            }
        })
    }

    /// Encodes a `Map` operation.
    fn encode_map(&mut self, op: MapOp) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        Ok(match op {
            MapOp::Empty => self
                .vcx
                .mk_map_empty_expr(vir::TYPE_PSNAP, vir::TYPE_PSNAP)
                .upcast_ty(),
            MapOp::Insert => {
                let map = *self.e_input(0)?.expect_builtin();
                let key = self.value_operand(1, Self::adt_type_arg(self.sig.inputs()[0], 0))?;
                let key = map.map_key_caster().cast_to_callee_ctx(key);
                let val = self.value_operand(2, Self::adt_type_arg(self.sig.inputs()[0], 1))?;
                let val = map.map_val_caster().cast_to_callee_ctx(val);
                self.vcx
                    .mk_map_update_expr(
                        self.operands[0].downcast_ty(),
                        key.downcast_ty::<vir::PSnap>(),
                        val.downcast_ty::<vir::PSnap>(),
                    )
                    .upcast_ty()
            }
            MapOp::Len => self
                .vcx
                .mk_collection_len_expr(self.operands[0].downcast_ty::<vir::Map>())
                .upcast_ty(),
            MapOp::Keys => self
                .vcx
                .mk_map_domain_expr(self.operands[0].downcast_ty())
                .upcast_ty(),
            MapOp::Values => self
                .vcx
                .mk_map_range_expr(self.operands[0].downcast_ty())
                .upcast_ty(),
            MapOp::Setminus => {
                let map_setminus = self
                    .deps
                    .require_ref::<CollectionOpsEnc>(CollectionOp::MapSetminus)?
                    .expect_map_setminus();
                map_setminus.call()(
                    self.operands[0].downcast_ty(),
                    self.operands[1].downcast_ty(),
                )
                .upcast_ty()
            }
            MapOp::Contains => {
                let map = *self.e_input(0)?.expect_builtin();
                let key = self.value_operand(1, Self::adt_type_arg(self.sig.inputs()[0], 0))?;
                let key = map.map_key_caster().cast_to_callee_ctx(key);
                self.vcx
                    .mk_map_contains_expr(
                        self.operands[0].downcast_ty(),
                        key.downcast_ty::<vir::PSnap>(),
                    )
                    .upcast_ty()
            }
            MapOp::Index => {
                let map_data = *self.e_input_deref(0)?.expect_builtin();
                let map = self.deref_operand(0)?;
                let self_ = self.sig.inputs()[0].builtin_deref(false).unwrap();
                let key = self.value_operand(1, Self::adt_type_arg(self_, 0))?;
                let key = map_data.map_key_caster().cast_to_callee_ctx(key);
                let val = if let Some(span) = self.span {
                    self.handle_partial_op_error(
                        "call.failed:map.key.contains",
                        "the map may not contain this key",
                        span,
                    );
                    self.vcx
                        .mk_map_lookup_expr(map, key.downcast_ty::<vir::PSnap>())
                        .downcast_ty::<vir::PSnap>()
                        .upcast_ty()
                } else {
                    let map_lookup = self
                        .deps
                        .require_ref::<CollectionOpsEnc>(CollectionOp::MapLookup)?
                        .expect_map_lookup();
                    map_lookup.call()(map, key.downcast_ty()).upcast_ty()
                };
                let val = map_data.map_val_caster().cast_to_caller_ctx(val);
                let val = self
                    .e_output_deref()?
                    .expect_structlike()
                    .field_snaps_to_snap(vec![val])
                    .upcast_ty();
                self.wrap_in_immref(val)?
            }
        })
    }

    /// Encodes a shared numeric operation on the native representation `T`
    /// (`vir::Int` for `Int`, `vir::Perm` for `Real`, per `real`); `From` is
    /// type-specific and handled by the caller.
    fn encode_num<T: vir::CompType>(
        &mut self,
        op: NumOp,
        real: bool,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Snap>>
    where
        vir::Prim: vir::TransmuteFrom<T>,
        vir::Snap: vir::TransmuteFrom<T>,
    {
        Ok(match op {
            NumOp::From => unreachable!("`From` is handled by the caller"),
            NumOp::Add | NumOp::Sub | NumOp::Mul | NumOp::Div | NumOp::Rem => {
                let kind = match (real, op) {
                    (false, NumOp::Add) => vir::BinOpKind::Add,
                    (false, NumOp::Sub) => vir::BinOpKind::Sub,
                    (false, NumOp::Mul) => vir::BinOpKind::Mul,
                    (false, NumOp::Div) => vir::BinOpKind::Div,
                    (false, NumOp::Rem) => vir::BinOpKind::Mod,
                    (true, NumOp::Add) => vir::BinOpKind::PermAdd,
                    (true, NumOp::Sub) => vir::BinOpKind::PermSub,
                    (true, NumOp::Mul) => vir::BinOpKind::PermMul,
                    (true, NumOp::Div) => vir::BinOpKind::PermPermDiv,
                    (true, NumOp::Rem) => unreachable!("`Real` has no `Rem`"),
                    _ => unreachable!(),
                };
                self.vcx
                    .mk_bin_op_expr(
                        kind,
                        self.operands[0].downcast_ty::<T>(),
                        self.operands[1].downcast_ty::<T>(),
                    )
                    .downcast_ty::<T>()
                    .upcast_ty()
            }
            NumOp::Neg => {
                let kind = if real {
                    vir::UnOpKind::PermNeg
                } else {
                    vir::UnOpKind::Neg
                };
                self.vcx
                    .mk_unary_op_expr(kind, self.operands[0].downcast_ty::<T>().upcast_ty())
                    .downcast_ty::<T>()
                    .upcast_ty()
            }
            NumOp::Lt | NumOp::Le | NumOp::Gt | NumOp::Ge => {
                let (v1, v2) = self.deref_operands::<T>()?;
                let bin_op = match op {
                    NumOp::Lt => vir::BinOpKind::CmpLt,
                    NumOp::Le => vir::BinOpKind::CmpLe,
                    NumOp::Gt => vir::BinOpKind::CmpGt,
                    NumOp::Ge => vir::BinOpKind::CmpGe,
                    _ => unreachable!(),
                };
                self.native_cmp(bin_op, v1, v2).upcast_ty()
            }
            NumOp::Cmp => {
                let (v1, v2) = self.deref_operands::<T>()?;
                self.encode_cmp(self.sig.output(), v1, v2)?.upcast_ty()
            }
            NumOp::PartialCmp => {
                let (v1, v2) = self.deref_operands::<T>()?;
                self.encode_partial_cmp(self.sig.output(), v1, v2)?
                    .upcast_ty()
            }
            // The `Ord` convenience methods take `self` by value. Tie
            // behavior is irrelevant on mathematical values, and `clamp`'s
            // `min <= max` panic precondition is not checked.
            NumOp::Max | NumOp::Min => {
                let v0 = self.operands[0].downcast_ty::<T>();
                let v1 = self.operands[1].downcast_ty::<T>();
                let cond = self.native_cmp(vir::BinOpKind::CmpLt, v1, v0);
                let (then, else_) = if op == NumOp::Max { (v0, v1) } else { (v1, v0) };
                self.vcx.mk_ternary_expr(cond, then, else_).upcast_ty()
            }
            NumOp::Clamp => {
                let v = self.operands[0].downcast_ty::<T>();
                let lo = self.operands[1].downcast_ty::<T>();
                let hi = self.operands[2].downcast_ty::<T>();
                let above =
                    self.vcx
                        .mk_ternary_expr(self.native_cmp(vir::BinOpKind::CmpGt, v, hi), hi, v);
                self.vcx
                    .mk_ternary_expr(self.native_cmp(vir::BinOpKind::CmpLt, v, lo), lo, above)
                    .upcast_ty()
            }
        })
    }

    /// The float snapshot domain for a `FloatTy`.
    fn float_domain(&mut self, fl: ty::FloatTy) -> EncResult<'vir, FloatDomain<'vir>> {
        let ty = match fl {
            ty::FloatTy::F16 => self.vcx.tcx().types.f16,
            ty::FloatTy::F32 => self.vcx.tcx().types.f32,
            ty::FloatTy::F64 => self.vcx.tcx().types.f64,
            ty::FloatTy::F128 => self.vcx.tcx().types.f128,
        };
        let ty = self
            .deps
            .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_prim_ty(ty))?;
        Ok(*ty.expect_float())
    }

    /// Registers a backtranslation handler for the well-definedness
    /// obligation of a checked (impure-code) partial collection operation.
    /// The handler attaches to this encoding's span - the call statement,
    /// which is part of the task key.
    fn handle_partial_op_error(&self, error_kind: &'static str, message: &'static str, span: Span) {
        self.vcx.handle_error(error_kind, move |_| {
            Some(vec![PrustiError::verification(message, span.into())])
        });
    }

    /// The snapshot of the `impl Value<T>` operand `i`, where `expected` is
    /// `T`: an operand of type `T` is used directly, one of type `&T` is
    /// dereferenced (note that `T` could itself be a reference, e.g. `&i32`).
    fn value_operand(
        &mut self,
        i: usize,
        expected: ty::Ty<'vir>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        let input = self.sig.inputs()[i];
        fn count_refs(mut ty: ty::Ty) -> usize {
            let mut count = 0;
            while let Some(inner) = BuiltinCtxt::deref_opt(ty) {
                count += 1;
                ty = inner;
            }
            count
        }
        let i_refs = count_refs(input);
        let e_refs = count_refs(expected);
        if i_refs == e_refs {
            Ok(self.operands[i])
        } else if i_refs == e_refs + 1 {
            Ok(self
                .e_input_immref(i)?
                .value_access(self.operands[i].downcast_ty()))
        } else {
            unreachable!(
                "`impl Value<T>` operand type `{input}` does not match \
                the expected value type `{expected}`"
            )
        }
    }

    /// The Viper `Int` of an index snapshot of Rust type `ty` (from
    /// `Index<I> where Int: From<I>`): the native snapshot for `Int` itself,
    /// or the primitive value of a Rust integer.
    fn index_to_int(
        &mut self,
        snap: ExprRet<'vir, vir::Snap>,
        ty: ty::Ty<'vir>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Int>> {
        let name = PrustiBuiltin::prusti_adt_name(self.vcx.tcx(), ty);
        if name.as_ref().map(|name| name.as_str()) == Some("Int") {
            Ok(snap.downcast_ty())
        } else {
            assert!(
                matches!(ty.kind(), ty::TyKind::Int(_) | ty::TyKind::Uint(_)),
                "unsupported sequence index type `{ty}`"
            );
            let prim = *self.encode_ty(ty)?.expect_primitive();
            Ok(prim.snap_to_prim(snap.downcast_ty()).downcast_ty())
        }
    }

    /// Wraps a referent snapshot in an immutable-reference snapshot (`null`
    /// address, ZST metadata): the builtin `Index` methods return `&T`, whose
    /// address is meaningless in specs (the value is immediately dereferenced).
    fn wrap_in_immref(
        &mut self,
        value: ExprRet<'vir, vir::Snap>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::Snap>> {
        let metadata_ty = self
            .sig
            .output()
            .pointee_metadata_ty_or_projection(self.vcx.tcx());
        // Resolve e.g. `<T as Pointee>::Metadata` to `()` when the context's
        // bounds prove `T: Sized` (`pointee_metadata_ty_or_projection` only
        // resolves bound-independent sizedness).
        let metadata_ty = self.args.context().normalize(metadata_ty);
        // This can only happen for `Ghost::deref` (the `index` functions all
        // return `&Ghost<T>`).
        let metadata = self.encode_ty(metadata_ty)?.zst_to_snap().ok_or_else(|| {
            EncodeFullError::DependencyError(vec![(
                PrustiBuiltinEnc::ENCODER_NAME,
                format!(
                    "Ghost::deref on maybe unsized `{:?}` not supported",
                    Self::deref_opt(self.sig.output()).unwrap()
                ),
                self.span.into_iter().collect(),
            )])
        })?;
        Ok(self
            .e_output_immref()?
            .prim_to_snap(self.vcx.mk_null().lazy(), metadata.upcast_ty(), value)
            .upcast_ty())
    }

    /// Dereferences the two `&self`/`&other` operand holes to their native
    /// value `T` (the `PartialOrd`/`PartialEq` methods take `&self`).
    fn deref_operands<T: vir::CompType>(
        &mut self,
    ) -> EncResult<'vir, (ExprRet<'vir, T>, ExprRet<'vir, T>)>
    where
        vir::Snap: vir::TransmuteFrom<T>,
    {
        Ok((self.deref_operand::<T>(0)?, self.deref_operand::<T>(1)?))
    }

    /// Dereferences the `&self`/`&other` operand `i` to its native value.
    fn deref_operand<T: vir::CompType>(&mut self, i: usize) -> EncResult<'vir, ExprRet<'vir, T>>
    where
        vir::Snap: vir::TransmuteFrom<T>,
    {
        let operand = self.operands[i].downcast_ty::<vir::CSnap>();
        Ok(self
            .e_input_immref(i)?
            .value_access(operand)
            .downcast_ty::<T>())
    }

    /// Comparison of two natively-represented builtin values (`Int`/`Real`).
    fn native_cmp<T: vir::CompType>(
        &self,
        bin_op: vir::BinOpKind,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> ExprRet<'vir, vir::Bool> {
        self.vcx
            .mk_bin_op_expr_inner(bin_op, val1.as_dyn(), val2.as_dyn())
            .downcast_ty()
    }

    /// Encodes `Ord::cmp` on a native builtin: builds the `Ordering` snapshot
    /// `if a < b { Less } else if a == b { Equal } else { Greater }`.
    fn encode_cmp<T: vir::CompType>(
        &mut self,
        ordering_ty: ty::Ty<'vir>,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::CSnap>> {
        // `core::cmp::Ordering`'s variants in definition order: Less, Equal, Greater.
        let ord = self.encode_ty(ordering_ty)?;
        let cmp = |bin_op| self.native_cmp(bin_op, val1, val2);
        let variant = |idx: usize| {
            ord.expect_variant_opt(Some(abi::VariantIdx::from_usize(idx)))
                .field_snaps_to_snap(Vec::new())
        };
        let (less, equal, greater) = (variant(0), variant(1), variant(2));

        let else_ = self
            .vcx
            .mk_ternary_expr(cmp(vir::BinOpKind::CmpEq), equal, greater);
        Ok(self
            .vcx
            .mk_ternary_expr(cmp(vir::BinOpKind::CmpLt), less, else_))
    }

    /// Encodes `PartialOrd::partial_cmp` on a native builtin: `Some(a.cmp(b))`.
    fn encode_partial_cmp<T: vir::CompType>(
        &mut self,
        option_ty: ty::Ty<'vir>,
        val1: ExprRet<'vir, T>,
        val2: ExprRet<'vir, T>,
    ) -> EncResult<'vir, ExprRet<'vir, vir::CSnap>> {
        let ordering_ty = Self::adt_type_arg(option_ty, 0);
        let ordering = self.encode_cmp(ordering_ty, val1, val2)?;

        // Wrap in `Option::Some` (variant 1, one field).
        let option = self.encode_ty(option_ty)?;
        Ok(option
            .expect_variant_opt(Some(abi::VariantIdx::from_usize(1)))
            .field_snaps_to_snap(vec![ordering.upcast_ty()]))
    }

    /// The encoding of the type of input `i`.
    fn e_input(&mut self, i: usize) -> EncResult<'vir, TyUsePure<'vir>> {
        self.encode_ty(self.sig.inputs()[i])
    }

    /// The encoding of dereferenced type of input `i` (i.e. `T` when the input
    /// is `&T`).
    fn e_input_deref(&mut self, i: usize) -> EncResult<'vir, TyUsePure<'vir>> {
        self.encode_ty(Self::deref(self.sig.inputs()[i]))
    }

    /// The encoding of the type of input `i`, which must be a shared reference.
    fn e_input_immref(&mut self, i: usize) -> EncResult<'vir, &'vir TyUsePureImmRef<'vir>> {
        Ok(self.e_input(i)?.expect_immref())
    }

    /// The encoding of the output type.
    fn e_output(&mut self) -> EncResult<'vir, TyUsePure<'vir>> {
        self.encode_ty(self.sig.output())
    }

    /// The encoding of the dereferenced output type (i.e. `T` when the output
    /// is `&T`).
    fn e_output_deref(&mut self) -> EncResult<'vir, TyUsePure<'vir>> {
        self.encode_ty(Self::deref(self.sig.output()))
    }

    /// The encoding of the output type, which must be a shared reference.
    fn e_output_immref(&mut self) -> EncResult<'vir, &'vir TyUsePureImmRef<'vir>> {
        Ok(self.e_output()?.expect_immref())
    }

    /// The encoding of a type used at this call site.
    fn encode_ty(&mut self, ty: ty::Ty<'vir>) -> EncResult<'vir, TyUsePure<'vir>> {
        self.deps
            .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(ty, self.args.context()))
    }

    /// Dereferences a `&T` type to `T`. Panics if `ty` is not a shared
    /// reference type.
    #[track_caller]
    fn deref(ty: ty::Ty<'vir>) -> ty::Ty<'vir> {
        Self::deref_opt(ty).unwrap_or_else(|| unreachable!("not a reference type: {ty:?}"))
    }

    fn deref_opt(ty: ty::Ty<'vir>) -> Option<ty::Ty<'vir>> {
        match ty.kind() {
            ty::TyKind::Ref(_, referent, ty::Mutability::Not) => Some(*referent),
            _ => None,
        }
    }

    /// The `idx`-th type argument of the ADT type `ty`.
    fn adt_type_arg(ty: ty::Ty<'vir>, idx: usize) -> ty::Ty<'vir> {
        let ty::TyKind::Adt(_, adt_args) = ty.kind() else {
            unreachable!("not an ADT type: {ty:?}");
        };
        adt_args.type_at(idx)
    }
}

/// The helper functions for the collection builtins, one per
/// [`CollectionOp`] key so that a program is only charged for the axioms of
/// the operations it actually uses:
///
/// - `SeqLookup`/`SeqUpdate`/`MapLookup` are *total* uninterpreted versions
///   of the native (partial) `s[i]`/`s[i := v]`/`m[k]`, axiomatized to agree
///   with them in bounds. Specs must use these since the `f_` encoding of a
///   pure function drops the precondition, so a partial operation in a
///   contract could never be proven well-formed.
/// - `SeqSliceFrom`/`SeqSliceTo` are *checked* slices (`s[a..]`/`s[..b]`)
///   for impure (ghost) code: program functions whose bound precondition is
///   verified at each application. A two-sided slice `s[a..b]` composes the
///   two.
/// - `MapSetminus` (key removal) has no native Viper correspondent at all;
///   it is total and axiomatized by its domain and its lookups.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
enum CollectionOp {
    SeqLookup,
    SeqUpdate,
    SeqSliceFrom,
    SeqSliceTo,
    MapLookup,
    MapSetminus,
}

/// The typed identifier of a [`CollectionOp`]'s function, obtained by
/// requiring the op from [`CollectionOpsEnc`] (which guarantees the function
/// is emitted).
#[derive(Debug, Clone, Copy)]
enum CollectionOpFn<'vir> {
    SeqLookup(FunctionIdn<'vir, (vir::Seq, vir::Int), vir::PSnap>),
    SeqUpdate(FunctionIdn<'vir, (vir::Seq, vir::Int, vir::PSnap), vir::Seq>),
    SeqSliceFrom(FunctionIdn<'vir, (vir::Seq, vir::Int), vir::Seq>),
    SeqSliceTo(FunctionIdn<'vir, (vir::Seq, vir::Int), vir::Seq>),
    MapLookup(FunctionIdn<'vir, (vir::Map, vir::PSnap), vir::PSnap>),
    MapSetminus(FunctionIdn<'vir, (vir::Map, vir::Set), vir::Map>),
}

impl task_encoder::OutputRefAny for CollectionOpFn<'_> {}

impl<'vir> CollectionOpFn<'vir> {
    pub fn expect_seq_lookup(self) -> FunctionIdn<'vir, (vir::Seq, vir::Int), vir::PSnap> {
        match self {
            Self::SeqLookup(fn_idn) => fn_idn,
            other => panic!("expected `SeqLookup`, got {other:?}"),
        }
    }

    pub fn expect_seq_update(
        self,
    ) -> FunctionIdn<'vir, (vir::Seq, vir::Int, vir::PSnap), vir::Seq> {
        match self {
            Self::SeqUpdate(fn_idn) => fn_idn,
            other => panic!("expected `SeqUpdate`, got {other:?}"),
        }
    }

    pub fn expect_seq_slice_from(self) -> FunctionIdn<'vir, (vir::Seq, vir::Int), vir::Seq> {
        match self {
            Self::SeqSliceFrom(fn_idn) => fn_idn,
            other => panic!("expected `SeqSliceFrom`, got {other:?}"),
        }
    }

    pub fn expect_seq_slice_to(self) -> FunctionIdn<'vir, (vir::Seq, vir::Int), vir::Seq> {
        match self {
            Self::SeqSliceTo(fn_idn) => fn_idn,
            other => panic!("expected `SeqSliceTo`, got {other:?}"),
        }
    }

    pub fn expect_map_lookup(self) -> FunctionIdn<'vir, (vir::Map, vir::PSnap), vir::PSnap> {
        match self {
            Self::MapLookup(fn_idn) => fn_idn,
            other => panic!("expected `MapLookup`, got {other:?}"),
        }
    }

    pub fn expect_map_setminus(self) -> FunctionIdn<'vir, (vir::Map, vir::Set), vir::Map> {
        match self {
            Self::MapSetminus(fn_idn) => fn_idn,
            other => panic!("expected `MapSetminus`, got {other:?}"),
        }
    }
}

#[derive(Clone)]
enum CollectionOpOutput<'vir> {
    /// The op's uninterpreted function and defining axioms; all members are
    /// merged into the single `PrustiCollectionOps` domain on emission.
    DomainMember(vir::DomainFunction<'vir>, Vec<vir::DomainAxiom<'vir>>),
    Function(vir::Function<'vir>),
}

struct CollectionOpsEnc;

impl TaskEncoder for CollectionOpsEnc {
    task_encoder::encoder_cache!(CollectionOpsEnc);
    const ENCODER_NAME: &'static str = "collection ops encoder";
    type TaskDescription<'vir> = CollectionOp;
    type OutputRef<'vir> = CollectionOpFn<'vir>;
    type OutputFullLocal<'vir> = CollectionOpOutput<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        vir::with_vcx(|vcx| {
            let seq_ty = vcx.mk_ty_seq(vir::TYPE_PSNAP);
            let (fn_ref, output) = match task_key {
                CollectionOp::SeqLookup => {
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_seq_lookup"),
                        (seq_ty, vir::TYPE_INT),
                        vir::TYPE_PSNAP,
                    );
                    (
                        CollectionOpFn::SeqLookup(fn_idn),
                        CollectionOpOutput::DomainMember(
                            vcx.mk_domain_function(fn_idn, false, None),
                            vec![Self::seq_lookup_axiom(vcx, fn_idn)],
                        ),
                    )
                }
                CollectionOp::SeqUpdate => {
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_seq_update"),
                        (seq_ty, vir::TYPE_INT, vir::TYPE_PSNAP),
                        seq_ty,
                    );
                    (
                        CollectionOpFn::SeqUpdate(fn_idn),
                        CollectionOpOutput::DomainMember(
                            vcx.mk_domain_function(fn_idn, false, None),
                            vec![Self::seq_update_axiom(vcx, fn_idn)],
                        ),
                    )
                }
                CollectionOp::SeqSliceFrom => {
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_seq_slice_from"),
                        (seq_ty, vir::TYPE_INT),
                        seq_ty,
                    );
                    (
                        CollectionOpFn::SeqSliceFrom(fn_idn),
                        CollectionOpOutput::Function(Self::seq_slice_one_sided_function(
                            vcx, fn_idn, false,
                        )),
                    )
                }
                CollectionOp::SeqSliceTo => {
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_seq_slice_to"),
                        (seq_ty, vir::TYPE_INT),
                        seq_ty,
                    );
                    (
                        CollectionOpFn::SeqSliceTo(fn_idn),
                        CollectionOpOutput::Function(Self::seq_slice_one_sided_function(
                            vcx, fn_idn, true,
                        )),
                    )
                }
                CollectionOp::MapLookup => {
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_map_lookup"),
                        (
                            vcx.mk_ty_map(vir::TYPE_PSNAP, vir::TYPE_PSNAP),
                            vir::TYPE_PSNAP,
                        ),
                        vir::TYPE_PSNAP,
                    );
                    (
                        CollectionOpFn::MapLookup(fn_idn),
                        CollectionOpOutput::DomainMember(
                            vcx.mk_domain_function(fn_idn, false, None),
                            vec![Self::map_lookup_axiom(vcx, fn_idn)],
                        ),
                    )
                }
                CollectionOp::MapSetminus => {
                    let map_ty = vcx.mk_ty_map(vir::TYPE_PSNAP, vir::TYPE_PSNAP);
                    let fn_idn = FunctionIdn::new(
                        vir::ViperIdent::new("prusti_map_setminus"),
                        (map_ty, vcx.mk_ty_set(vir::TYPE_PSNAP)),
                        map_ty,
                    );
                    (
                        CollectionOpFn::MapSetminus(fn_idn),
                        CollectionOpOutput::DomainMember(
                            vcx.mk_domain_function(fn_idn, false, None),
                            Self::map_setminus_axioms(vcx, fn_idn),
                        ),
                    )
                }
            };
            deps.emit_output_ref(*task_key, fn_ref)?;
            Ok((output, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let mut functions = Vec::new();
        let mut axioms = Vec::new();
        for output in Self::all_outputs_local_no_errors(program) {
            match output {
                CollectionOpOutput::DomainMember(function, axs) => {
                    functions.push(function);
                    axioms.extend(axs);
                }
                CollectionOpOutput::Function(function) => program.add_function(function),
            }
        }
        if !functions.is_empty() {
            vir::with_vcx(|vcx| {
                program.add_domain(vcx.mk_domain(
                    vir::ViperIdent::new("PrustiCollectionOps"),
                    &[],
                    vcx.alloc_slice(&axioms),
                    vcx.alloc_slice(&functions),
                    None,
                ))
            });
        }
    }
}

impl CollectionOpsEnc {
    /// `0 <= i && i < |seq|`.
    fn in_bounds<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        i: vir::ExprInt<'vir>,
        seq: vir::ExprSeq<'vir>,
    ) -> vir::ExprBool<'vir> {
        let zero = vcx.mk_uint::<0>();
        vir::expr! { vcx; ((zero) <= (i)) && ((i) < (|seq|)) }
    }

    // forall s, i :: { seq_lookup(s, i) }
    //     0 <= i && i < |s| ==> seq_lookup(s, i) == s[i]
    fn seq_lookup_axiom<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        fn_idn: FunctionIdn<'vir, (vir::Seq, vir::Int), vir::PSnap>,
    ) -> vir::DomainAxiom<'vir> {
        let s_decl = vcx.mk_local_decl("s", vcx.mk_ty_seq(vir::TYPE_PSNAP));
        let i_decl = vcx.mk_local_decl("i", vir::TYPE_INT);
        let s = vcx.mk_local_ex(s_decl);
        let i = vcx.mk_local_ex(i_decl);
        let sl = fn_idn(s, i);
        let guard = Self::in_bounds(vcx, i, s);
        vcx.mk_domain_axiom(
            vir::ViperIdent::new("prusti_seq_lookup_native"),
            vir::expr! { vcx;
                forall [s_decl], [i_decl] :: {[sl]} (guard) ==> ((sl) == (((s)[i]) as PSnap))
            },
        )
    }

    // forall s, i, v :: { seq_update(s, i, v) }
    //     0 <= i && i < |s| ==> seq_update(s, i, v) == s[i := v]
    fn seq_update_axiom<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        fn_idn: FunctionIdn<'vir, (vir::Seq, vir::Int, vir::PSnap), vir::Seq>,
    ) -> vir::DomainAxiom<'vir> {
        let s_decl = vcx.mk_local_decl("s", vcx.mk_ty_seq(vir::TYPE_PSNAP));
        let i_decl = vcx.mk_local_decl("i", vir::TYPE_INT);
        let v_decl = vcx.mk_local_decl("v", vir::TYPE_PSNAP);
        let s = vcx.mk_local_ex(s_decl);
        let i = vcx.mk_local_ex(i_decl);
        let v = vcx.mk_local_ex(v_decl);
        let su = fn_idn(s, i, v);
        let upd = vcx.mk_seq_update_expr(s, i, v);
        let guard = Self::in_bounds(vcx, i, s);
        vcx.mk_domain_axiom(
            vir::ViperIdent::new("prusti_seq_update_native"),
            vir::expr! { vcx;
                forall [s_decl], [i_decl], [v_decl] :: {[su]} (guard) ==> ((su) == (upd))
            },
        )
    }

    // forall m, k :: { map_lookup(m, k) }
    //     k in m ==> map_lookup(m, k) == m[k]
    fn map_lookup_axiom<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        fn_idn: FunctionIdn<'vir, (vir::Map, vir::PSnap), vir::PSnap>,
    ) -> vir::DomainAxiom<'vir> {
        let m_decl = vcx.mk_local_decl("m", vcx.mk_ty_map(vir::TYPE_PSNAP, vir::TYPE_PSNAP));
        let k_decl = vcx.mk_local_decl("k", vir::TYPE_PSNAP);
        let m = vcx.mk_local_ex(m_decl);
        let k = vcx.mk_local_ex(k_decl);
        let ml = fn_idn(m, k);
        vcx.mk_domain_axiom(
            vir::ViperIdent::new("prusti_map_lookup_native"),
            vir::expr! { vcx;
                forall [m_decl], [k_decl] :: {[ml]} ((k) in (m)) ==> ((ml) == (((m)[k]) as PSnap))
            },
        )
    }

    // forall m, s :: { prusti_map_setminus(m, s) }
    //     domain(prusti_map_setminus(m, s)) == domain(m) setminus s
    // forall m, s, k :: { prusti_map_setminus(m, s)[k] }
    //     k in domain(m) && !(k in s) ==> prusti_map_setminus(m, s)[k] == m[k]
    fn map_setminus_axioms<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        fn_idn: FunctionIdn<'vir, (vir::Map, vir::Set), vir::Map>,
    ) -> Vec<vir::DomainAxiom<'vir>> {
        let m_decl = vcx.mk_local_decl("m", vcx.mk_ty_map(vir::TYPE_PSNAP, vir::TYPE_PSNAP));
        let s_decl = vcx.mk_local_decl("s", vcx.mk_ty_set(vir::TYPE_PSNAP));
        let k_decl = vcx.mk_local_decl("k", vir::TYPE_PSNAP);
        let m = vcx.mk_local_ex(m_decl);
        let s = vcx.mk_local_ex(s_decl);
        let k = vcx.mk_local_ex(k_decl);
        let ms = fn_idn(m, s);
        let domain_axiom = vcx.mk_domain_axiom(
            vir::ViperIdent::new("prusti_map_setminus_domain"),
            vir::expr! { vcx;
                forall [m_decl], [s_decl] :: {[ms]}
                    (domain(ms)) == (((domain(m)) setminus (s)) as Set)
            },
        );
        let ms_lookup = vcx.mk_map_lookup_expr(ms, k);
        let lookup_axiom = vcx.mk_domain_axiom(
            vir::ViperIdent::new("prusti_map_setminus_lookup"),
            vir::expr! { vcx;
                forall [m_decl], [s_decl], [k_decl] :: {[ms_lookup]}
                    (((k) in (m)) && (!((k) in (s)))) ==> (((ms_lookup) as PSnap) == (((m)[k]) as PSnap))
            },
        );
        vec![domain_axiom, lookup_axiom]
    }

    // function prusti_seq_slice(s: Seq[s_Param], lo: Int, hi: Int): Seq[s_Param]
    //     requires 0 <= lo && lo <= hi && hi <= |s|
    // { drop(take(s, hi), lo) }
    /// The one-sided checked slices: `prusti_seq_slice_to(s, i)` (`take`,
    /// the native `s[..i]`) or `prusti_seq_slice_from(s, i)` (the native
    /// `s[i..]`), with the bound checked by the precondition.
    fn seq_slice_one_sided_function<'vir>(
        vcx: &'vir vir::VirCtxt<'vir>,
        fn_idn: FunctionIdn<'vir, (vir::Seq, vir::Int), vir::Seq>,
        take: bool,
    ) -> vir::Function<'vir> {
        let s_decl = vcx.mk_local_decl("s", vcx.mk_ty_seq(vir::TYPE_PSNAP));
        let i_decl = vcx.mk_local_decl("i", vir::TYPE_INT);
        let s = vcx.mk_local_ex(s_decl);
        let i = vcx.mk_local_ex(i_decl);
        let zero = vcx.mk_uint::<0>();
        let lower = vir::expr! { vcx; (zero) <= (i) };
        let upper = vir::expr! { vcx; (i) <= (|s|) };
        let body = if take {
            vcx.mk_seq_take_expr(s, i)
        } else {
            vcx.mk_seq_drop_expr(s, i)
        };
        vcx.mk_function(
            fn_idn,
            (s_decl, i_decl),
            vcx.alloc_slice(&[lower, upper]),
            &[],
            None,
            Some(body),
        )
    }
}
