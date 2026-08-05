use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullError, OutputRefAny, TaskEncoder};
use vir::CastType;

use crate::encoders::{
    FunctionCallEnc, TyUsePureEnc,
    custom::{PairUse, PairUseEnc},
    mir_fn::CallTaskDescription,
    ty::{
        RustTy, RustTyDatas, RustTyDecomposition,
        data::{EnumData, StructData, TyDatas, TySpecifics},
        generics::{GArgsTy, GArgsTyEnc, GParams, GenericParamsEnc, ty_identity_expr},
        impure::{ImpureTyDatas, TyImpureEnc},
        pure::{PureTyDatas, TyPureEnc},
    },
};

#[derive(Debug, Clone, Copy)]
pub struct TyInteriorMutUseExpr<'vir> {
    /// `s_Ty_IM_inner`: the set of interior-mutable objects with full (write)
    /// permission (from `#[interior_mut]` without a permission expression, e.g.
    /// `Cell`/`UnsafeCell`), reachable at any nesting depth.
    inner: InteriorMutFn<'vir>,
    /// `s_Ty_IM_object`: the set of interior-mutable objects with a
    /// permission-amount expression (from `#[interior_mut(EXPR)]`, e.g.
    /// `RefCell`), reachable at any nesting depth. Takes the inner-IM QP `Map`
    /// snapshot as an extra argument.
    object: InteriorMutObjectFn<'vir>,
    args: GArgsTy<'vir>,
}

impl<'vir> TyInteriorMutUseExpr<'vir> {
    /// The full-permission (inner-IM) set of objects reachable from `addr`/`snap`.
    pub fn get_all_inner(
        &self,
        addr: vir::ExprRef<'vir>,
        snap: vir::ExprSnap<'vir>,
    ) -> vir::ExprSet<'vir> {
        (self.inner)(addr, snap, self.args.get_ty(), self.args.get_const())
    }

    /// The permission-expression (object-IM) set of objects reachable from
    /// `addr`/`snap`. `inner_map` is the `Map` snapshot of the inner-IM QP
    /// (so permission expressions can read the inner interior-mutable state).
    pub fn get_all_object(
        &self,
        addr: vir::ExprRef<'vir>,
        snap: vir::ExprSnap<'vir>,
        inner_map: vir::ExprMap<'vir>,
    ) -> vir::ExprSet<'vir> {
        (self.object)(
            addr,
            snap,
            inner_map,
            self.args.get_ty(),
            self.args.get_const(),
        )
    }
}

#[derive(Debug, Clone, Copy)]
pub enum TyInteriorMutError {
    NestedInteriorMut,
}

pub struct TyInteriorMutUseEnc;

impl TaskEncoder for TyInteriorMutUseEnc {
    task_encoder::encoder_cache!(TyInteriorMutUseEnc);
    const ENCODER_NAME: &'static str = "interior mutability use encoder";
    type TaskDescription<'vir> = RustTyDecomposition<'vir>;
    type OutputFullDependency<'vir> = TyInteriorMutUseExpr<'vir>;
    type EncodingError = TyInteriorMutError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let r = deps.require_ref::<TyInteriorMutEnc>(task_key.ty)?;
        let args = deps.require_dep::<GArgsTyEnc>(task_key.args)?;
        Ok((
            (),
            TyInteriorMutUseExpr {
                inner: r.inner,
                object: r.object,
                args,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyInteriorMutEnc::emit_outputs(program);
        QpToMapEnc::emit_outputs(program);
        super::generics::interior_mut::InteriorMutGenericsEnc::emit_outputs(program);
    }
}

/// The fixed name of the inner-IM-QP `Map` parameter threaded into
/// `#[pure_unstable]` functions' Viper encoding.
pub const PURE_UNSTABLE_INNER_MAP: &str = "inner_im_map";

/// The type of the inner-IM-QP snapshot `Map[Pair2[Ref, Type], s_Param]` that
/// `#[pure_unstable]` functions take as an extra Viper argument.
pub fn pure_unstable_inner_map_ty<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
) -> Result<vir::TypeMap<'vir>, EncodeFullError<'vir, E>> {
    let pair = deps
        .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
        .unwrap();
    Ok(vir::with_vcx(|vcx| vcx.mk_ty_map(pair.ty, vir::TYPE_PSNAP)))
}

/// The `LocalDecl` for the inner-IM-QP `Map` parameter of a `#[pure_unstable]`
/// function. Built with a fixed name so the function signature ([`FunctionEnc`])
/// and the body encoding ([`MirPureEnc`], which forwards it to nested
/// `#[pure_unstable]` callees) agree on it.
pub fn pure_unstable_inner_map_decl<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
) -> Result<vir::LocalDeclMap<'vir>, EncodeFullError<'vir, E>> {
    let ty = pure_unstable_inner_map_ty(deps)?;
    Ok(vir::with_vcx(|vcx| {
        vcx.mk_local_decl(PURE_UNSTABLE_INNER_MAP, ty)
    }))
}

/// Materializes the inner-IM QP (over `inner_set`) into its `Map` snapshot via
/// the `qp_to_map` function. The caller must hold the inner-IM QP permission at
/// the point this expression is evaluated.
pub fn interior_mut_inner_map<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    inner_set: vir::ExprSet<'vir>,
) -> Result<vir::ExprMap<'vir>, EncodeFullError<'vir, E>> {
    let qp_to_map = deps.require_dep::<QpToMapEnc>(())?;
    Ok(qp_to_map(inner_set))
}

/// The inner-IM-QP `Map` argument for a call to a `#[pure_unstable]` function
/// from a context that does not itself carry the map: an impure body, or a
/// spec/assertion of an impure method. There the heap is available at the
/// position the expression lands in, so the map is materialized on the spot
/// via `qp_to_map` over the union of the callee arguments' inner-IM sets (the
/// same sets the enclosing method's boundary QPs range over, so `qp_to_map`'s
/// precondition is dischargeable from the held QP).
///
/// `args` provides, per callee argument, its type decomposition, an address
/// expression, and its snapshot. The address may be a dummy (`null`) for
/// reference arguments: their inner-IM set functions read through the
/// snapshot's deref address and ignore the top-level address parameter.
pub(crate) fn pure_unstable_call_map<'vir, Curr: 'vir, Next: 'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    args: &[(
        RustTyDecomposition<'vir>,
        vir::ExprGenRef<'vir, Curr, Next>,
        vir::ExprGenSnap<'vir, Curr, Next>,
    )],
) -> Result<vir::ExprGenMap<'vir, Curr, Next>, EncodeFullError<'vir, E>> {
    let pair = deps
        .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
        .unwrap();
    let qp_to_map = deps.require_dep::<QpToMapEnc>(())?;
    let mut sets = Vec::new();
    for (ty, addr, snap) in args {
        let im = deps.require_dep::<TyInteriorMutUseEnc>(*ty)?;
        sets.push(im.inner.call()(
            *addr,
            *snap,
            im.args.get_ty(),
            im.args.get_const(),
        ));
    }
    Ok(vir::with_vcx(|vcx| {
        let set = sets
            .into_iter()
            .reduce(|a, b| {
                vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, a, b)
                    .downcast_ty()
            })
            .unwrap_or_else(|| vcx.mk_set_literal_expr(&[], pair.ty));
        qp_to_map.call()(set)
    }))
}

pub(super) struct TyInteriorMutEnc;

pub(crate) type InteriorMutFn<'vir> =
    vir::FunctionIdn<'vir, (vir::Ref, vir::Snap, vir::ManyTyVal, vir::ManyCSnap), vir::Set>;

/// The object-IM set function additionally takes the `Map` snapshot of the
/// inner-IM QP (`Map[Pair2[Ref, Type], s_Param]`), so that permission
/// expressions can read the inner interior-mutable state (e.g. a `RefCell`'s
/// borrow count) through it.
pub(crate) type InteriorMutObjectFn<'vir> = vir::FunctionIdn<
    'vir,
    (vir::Ref, vir::Snap, vir::Map, vir::ManyTyVal, vir::ManyCSnap),
    vir::Set,
>;

#[derive(Debug, Clone, Copy)]
pub(super) struct TyInteriorMutRef<'vir> {
    pub(super) inner: InteriorMutFn<'vir>,
    pub(super) object: InteriorMutObjectFn<'vir>,
}

impl<'vir> OutputRefAny for TyInteriorMutRef<'vir> {}

/// The two disjoint interior-mutability sets of a type: `inner` collects the
/// full-permission objects (`#[interior_mut]` without a perm expression),
/// `object` collects the permission-expression objects (`#[interior_mut(EXPR)]`).
#[derive(Clone, Copy)]
struct ImSets<'vir> {
    inner: vir::ExprSet<'vir>,
    object: vir::ExprSet<'vir>,
}

fn set_union<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    lhs: vir::ExprSet<'vir>,
    rhs: vir::ExprSet<'vir>,
) -> vir::ExprSet<'vir> {
    vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, lhs, rhs)
        .downcast_ty()
}

impl TaskEncoder for TyInteriorMutEnc {
    task_encoder::encoder_cache!(TyInteriorMutEnc);
    const ENCODER_NAME: &'static str = "interior mutability encoder";
    type TaskDescription<'vir> = RustTy<'vir>;

    type OutputRef<'vir> = TyInteriorMutRef<'vir>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;

    type EncodingError = TyInteriorMutError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        // TODO: remove
        let task_key: &RustTy = task_key;
        vir::with_vcx(|vcx| {
            let tuple = deps
                .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
                .unwrap();
            // The object-IM set elements are `(address, type, perm)` triples:
            // the permission amount (from `#[interior_mut(EXPR)]`) is baked into
            // the third component.
            let triple = deps
                .require_dep::<PairUseEnc>(vec![
                    vir::TYPE_REF.as_dyn(),
                    vir::TYPE_TYVAL.as_dyn(),
                    vir::TYPE_PERM.as_dyn(),
                ])
                .unwrap();

            let pure = deps.require_dep::<TyPureEnc>(*task_key)?;
            let impure = deps.require_dep::<TyImpureEnc>(*task_key)?;
            let params = deps
                .require_dep::<GenericParamsEnc>(task_key.params)
                .unwrap();
            let addr = vcx.mk_local_decl("addr", vir::TYPE_REF);
            let snap = vcx.mk_local_decl("snap", pure.snapshot);
            // The inner-IM QP `Map` snapshot, passed to the object-IM function.
            let inner_map_ty = vcx.mk_ty_map(tuple.ty, vir::TYPE_PSNAP);
            let inner_map = vcx.mk_local_decl("inner_map", inner_map_ty);
            let inner_result = vcx.mk_ty_set(tuple.ty);
            let object_result = vcx.mk_ty_set(triple.ty);
            let inner_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{}_IM_inner", task_key.name.as_str()),
                (addr.ty, snap.ty, params.ty_args(), params.const_args()),
                inner_result,
            );
            let object_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{}_IM_object", task_key.name.as_str()),
                (
                    addr.ty,
                    snap.ty,
                    inner_map.ty,
                    params.ty_args(),
                    params.const_args(),
                ),
                object_result,
            );
            deps.emit_output_ref(
                *task_key,
                TyInteriorMutRef {
                    inner: inner_idn,
                    object: object_idn,
                },
            )?;

            let addr_ex = vcx.mk_local_ex(addr);
            let snap_ex = vcx.mk_local_ex(snap);
            let inner_map_ex = vcx.mk_local_ex(inner_map);
            let tuple_ty = tuple.ty;
            let triple_ty = triple.ty;
            let mut field_enc = TyInteriorMutField {
                vcx,
                tuple,
                triple,
                deps,
                params: task_key.params,
                param_exprs: params.ty_exprs(),
                const_exprs: params.const_exprs(),
                addr: addr_ex,
                snap: snap_ex,
                inner_map: inner_map_ex,
            };
            let ty = vcx.alloc(pure.zip(impure));
            let empty_sets = ImSets {
                inner: vcx.mk_set_literal_expr(&[], tuple_ty),
                object: vcx.mk_set_literal_expr(&[], triple_ty),
            };
            // The recursive (field/ref) contributions, split into inner-IM and
            // object-IM sets.
            let body: Option<ImSets> = match &task_key.zip(ty).specifics {
                _ if task_key.unsafe_cell => Some(empty_sets),
                TySpecifics::Primitive(_) => Some(empty_sets),
                // A raw pointer gives no permission to its pointee, so it
                // contributes no interior-mutable objects.
                TySpecifics::Raw(_) => Some(empty_sets),
                TySpecifics::Param(_) => None,
                TySpecifics::Opaque(_) => None,
                TySpecifics::ImmRef(data) => Some(field_enc.all_in_immref(data)?),
                TySpecifics::MutRef(data) => Some(field_enc.all_in_mutref(data)?),
                // Builtins (e.g. `Real`) have no interior-mutable objects.
                TySpecifics::Builtin(_) => Some(empty_sets),
                TySpecifics::ArrayLike(_) => todo!(),
                TySpecifics::StructLike(data) => Some(field_enc.all_in_struct(data)?),
                TySpecifics::EnumLike(enum_data) => Some(field_enc.all_in_enum(enum_data)?),
            };
            // This type's own `#[interior_mut]` objects (e.g. the `*mut T` of a
            // `Cell`/`RefCell`), partitioned by whether they carry a permission
            // expression: those with one go to the object-IM set, those without
            // to the inner-IM set (full permission).
            let mut own_inner = Vec::new();
            let mut own_object = Vec::new();
            for im in task_key.interior_mut.iter() {
                let call = CallTaskDescription::new(
                    task_key.data.params,
                    task_key.data.params.rust_params(),
                    *im,
                );
                let signature = vcx.tcx().fn_sig(*im).skip_binder();
                let input = signature.inputs().skip_binder()[0];
                let input = RustTyDecomposition::from_ty(input, task_key.data.params);
                let metadata_ty = input
                    .ty
                    .ref_data()
                    .unwrap()
                    .metadata
                    .decompose_normalize(input.args);
                let metadata = match field_enc
                    .deps
                    .require_dep::<TyUsePureEnc>(metadata_ty)
                    .unwrap()
                    .zst_to_snap()
                {
                    Some(m) => m.upcast_ty(),
                    // The receiver is not statically thin (e.g. the accessor is
                    // on `impl<T: ?Sized>`). The metadata value is irrelevant
                    // for the accessor call, so use the arbitrary (but
                    // deterministic) unreachable snapshot to keep the IM set
                    // consistent across states.
                    None => field_enc
                        .deps
                        .require_ref::<TyUsePureEnc>(metadata_ty)
                        .unwrap()
                        .unreachable_to_snap(),
                };
                let input = field_enc
                    .deps
                    .require_dep::<TyUsePureEnc>(input)
                    .unwrap()
                    .expect_immref()
                    .prim_to_snap(addr_ex, metadata, snap_ex);
                let output = signature.output().skip_binder();
                let (inner, mut_) = match *output.kind() {
                    ty::TyKind::RawPtr(inner, mut_) => (inner, mut_),
                    _ => panic!(
                        "expected raw pointer output for interior mutability, got {:?}",
                        output
                    ),
                };
                let result = field_enc
                    .deps
                    .require_dep::<FunctionCallEnc>(call)
                    .unwrap()
                    .call_pure(vec![input.upcast_ty()]);
                let raw_ptr_to_ref = field_enc.deps.require_dep::<RawPtrToRefEnc>(mut_).unwrap();
                let ref_ = raw_ptr_to_ref(result.downcast_ty());
                let ty_ = RustTyDecomposition::from_ty(inner, task_key.data.params);
                let ty_expr = ty_identity_expr(field_enc.deps, ty_);
                // A permission expression (`#[interior_mut(EXPR)]`) means the
                // element belongs to the object-IM set (with the evaluated
                // permission amount baked in as the third tuple component);
                // otherwise it goes to the inner-IM set (full permission).
                if let Some(perm_def_id) = crate::encoders::get_interior_mut_perm(*im) {
                    let perm = field_enc.eval_perm(perm_def_id, input, task_key.data.params)?;
                    let triple = (field_enc.triple.constructor)(&[
                        ref_.as_dyn(),
                        ty_expr.as_dyn(),
                        perm.as_dyn(),
                    ]);
                    own_object.push(triple);
                } else {
                    let pair = (field_enc.tuple.constructor)(&[ref_.as_dyn(), ty_expr.as_dyn()]);
                    own_inner.push(pair);
                }
            }
            assert!(body.is_some() || (own_inner.is_empty() && own_object.is_empty()));

            // Combine the recursive contributions with this type's own objects.
            let combine = |recursive: Option<vir::ExprSet<'vir>>,
                           own: &[vir::Expr<'vir, vir::Pair>],
                           elem_ty: vir::Type<'vir, _>| {
                recursive.map(|recursive| {
                    if own.is_empty() {
                        recursive
                    } else {
                        let own = vcx.mk_set_literal_expr(vcx.alloc_slice(own), elem_ty);
                        set_union(vcx, recursive, own)
                    }
                })
            };
            let inner_set = combine(body.map(|b| b.inner), &own_inner, tuple_ty);
            let object_set = combine(body.map(|b| b.object), &own_object, triple_ty);
            let mk_post = |set: Option<vir::ExprSet<'vir>>| {
                set.map(|set| vcx.mk_eq_expr(vcx.mk_result(set.ty()), set))
                    .into_iter()
                    .collect::<Vec<_>>()
            };
            let inner_fn = vcx.mk_function(
                inner_idn,
                (addr, snap, params.ty_decls(), params.const_decls()),
                &[],
                vcx.alloc_slice(&mk_post(inner_set)),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            // The object-IM QP grants permission to `p_Param(im._3_0, im._3_1)`
            // for each `(ref, type, perm)` triple `im` in this set. Viper
            // requires that QP receiver to be injective, but it drops the third
            // (perm) component, so it is not injective over an arbitrary set of
            // triples. Each interior-mutable object does, however, have a unique
            // `(ref, type)` (which determines its permission), so we assume that
            // here. This is added unconditionally (even when `object_set` is
            // `None`, i.e. for the abstract `s_Param_IM_object`, whose result is
            // axiomatised to equal an injective concrete set): all these
            // functions are abstract (no body), so the postcondition is taken as
            // an axiom, and the QP (which quantifies over the generic
            // `s_Param_IM_object`) then passes the receiver injectivity check.
            let mut object_posts = mk_post(object_set);
            object_posts.push(field_enc.object_injective_post(object_result));
            object_posts.push(field_enc.object_nonneg_post(object_result));
            let object_fn = vcx.mk_function(
                object_idn,
                (
                    addr,
                    snap,
                    inner_map,
                    params.ty_decls(),
                    params.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&object_posts),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            let output = vec![inner_fn, object_fn];
            Ok((output, ()))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let outputs = Self::all_outputs_local_no_errors(program);
        for output in outputs {
            for func in output {
                program.add_function(func);
            }
        }
        RawPtrToRefEnc::emit_outputs(program);
    }
}

struct TyInteriorMutField<'a, 'vir> {
    vcx: &'vir vir::VirCtxt<'vir>,
    tuple: PairUse<'vir>,
    /// The `(Ref, Type, Perm)` triple used for object-IM set elements.
    triple: PairUse<'vir>,
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyInteriorMutEnc>,
    params: GParams<'vir>,
    param_exprs: &'a [vir::ExprTyVal<'vir>],
    const_exprs: &'a [vir::ExprCSnap<'vir>],
    addr: vir::ExprRef<'vir>,
    snap: vir::ExprSnap<'vir>,
    /// The inner-IM QP `Map` snapshot of the object function being built, passed
    /// down to nested object-IM set functions.
    inner_map: vir::ExprMap<'vir>,
}

impl<'vir> TyInteriorMutField<'_, 'vir> {
    fn empty_sets(&self) -> ImSets<'vir> {
        ImSets {
            inner: self.vcx.mk_set_literal_expr(&[], self.tuple.ty),
            object: self.vcx.mk_set_literal_expr(&[], self.triple.ty),
        }
    }

    /// The (assumed) injectivity postcondition for an object-IM set function:
    /// `forall a, b in result :: a._3_0 == b._3_0 && a._3_1 == b._3_1 ==> a == b`
    /// i.e. the `(ref, type)` of each triple uniquely determines the triple
    /// (including its permission). `set_ty` is the function's `Set[Pair3]`
    /// result type.
    fn object_injective_post(&self, set_ty: vir::TypeSet<'vir>) -> vir::ExprBool<'vir> {
        let vcx = self.vcx;
        let result: vir::ExprSet<'vir> = vcx.mk_result(set_ty);
        let a = vcx.mk_local_decl("a", self.triple.ty);
        let b = vcx.mk_local_decl("b", self.triple.ty);
        let a_ex = vcx.mk_local_ex(a);
        let b_ex = vcx.mk_local_ex(b);
        let a_in = vcx.mk_set_in_expr(a_ex, result);
        let b_in = vcx.mk_set_in_expr(b_ex, result);
        let key_eq = |i: usize| {
            vcx.mk_eq_expr(
                self.triple.destructors[i].call()(a_ex),
                self.triple.destructors[i].call()(b_ex),
            )
        };
        let antecedent = vcx.mk_conj(&[a_in, b_in, key_eq(0), key_eq(1)]);
        let body = vcx
            .mk_bin_op_expr(
                vir::BinOpKind::Implies,
                antecedent,
                vcx.mk_eq_expr(a_ex, b_ex),
            )
            .downcast_ty();
        vcx.mk_forall_expr(
            vcx.alloc_slice(&[a, b]),
            vcx.alloc_slice(&[vcx.mk_trigger(&[a_in, b_in])]),
            body,
        )
    }

    /// The (assumed) nonnegativity postcondition for an object-IM set
    /// function: every triple's permission amount is nonnegative. Object QPs
    /// over such sets need this to be well-formed (a QP amount must be
    /// provably nonnegative).
    fn object_nonneg_post(&self, set_ty: vir::TypeSet<'vir>) -> vir::ExprBool<'vir> {
        let vcx = self.vcx;
        let result: vir::ExprSet<'vir> = vcx.mk_result(set_ty);
        let im = vcx.mk_local_decl("im", self.triple.ty);
        let im_ex = vcx.mk_local_ex(im);
        let im_in = vcx.mk_set_in_expr(im_ex, result);
        let amount = self.triple.destructors[2].call()(im_ex).downcast_ty::<vir::Perm>();
        let zero = vcx
            .mk_bin_op_expr(
                vir::BinOpKind::FracPerm,
                vcx.mk_const_expr(vir::ConstData::Int(0)),
                vcx.mk_const_expr(vir::ConstData::Int(1)),
            )
            .downcast_ty::<vir::Perm>();
        let nonneg = vcx
            .mk_bin_op_expr(vir::BinOpKind::PermGeCmp, amount, zero)
            .downcast_ty();
        let body = vcx
            .mk_bin_op_expr(vir::BinOpKind::Implies, im_in, nonneg)
            .downcast_ty();
        vcx.mk_forall_expr(
            vcx.alloc_slice(&[im]),
            vcx.alloc_slice(&[vcx.mk_trigger(&[im_in])]),
            body,
        )
    }

    /// Evaluates the `#[interior_mut(EXPR)]` permission expression (the spec
    /// closure `perm_def_id`, taking the interior-mutable object's `self`
    /// snapshot `input`) into a Viper `Perm` amount.
    fn eval_perm(
        &mut self,
        perm_def_id: DefId,
        input: vir::ExprCSnap<'vir>,
        params: GParams<'vir>,
    ) -> Result<vir::ExprPerm<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let call = CallTaskDescription::new(params, params.rust_params(), perm_def_id);
        let inner_map = self.inner_map;
        let perm_func = self.deps.require_dep::<FunctionCallEnc>(call).unwrap();
        let args = vec![input.upcast_ty()];
        // The perm closure is `#[pure_unstable]`, so it takes the inner-IM-QP
        // `Map` (this object function's `inner_map` parameter) to read the
        // current interior-mutable state (e.g. a `RefCell`'s borrow count).
        let perm_snap = if perm_func.is_pure_unstable() {
            perm_func.call_pure_unstable(args, inner_map)
        } else {
            perm_func.call_pure(args)
        };
        // `Real` is represented natively as Viper `Perm`, so the returned
        // snapshot is the permission amount directly.
        Ok(perm_snap.downcast_ty())
    }

    /// A mutable reference also grants all interior-mutable objects reachable
    /// through it, computed like [`Self::all_in_immref`] from the referent
    /// value in the reference's snapshot.
    fn all_in_mutref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::MutRefData,
    ) -> Result<ImSets<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;

        let addr = pure.deref_access.call()(self.snap.downcast_ty());
        let snap = pure.value_access.call()(self.snap.downcast_ty());
        Ok(ImSets {
            inner: inner.get_all_inner(addr, snap.upcast_ty()),
            object: inner.get_all_object(addr, snap.upcast_ty(), self.inner_map),
        })
    }

    fn all_in_immref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::ImmRefData,
    ) -> Result<ImSets<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;

        let addr = pure.deref_access.call()(self.snap.downcast_ty());
        let snap = pure.value_access.call()(self.snap.downcast_ty());
        Ok(ImSets {
            inner: inner.get_all_inner(addr, snap.upcast_ty()),
            object: inner.get_all_object(addr, snap.upcast_ty(), self.inner_map),
        })
    }

    fn all_in_struct(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<ImSets<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let vcx = self.vcx;
        data.fields
            .iter()
            .map(|(field, (pure, impure))| {
                let ty = field.decompose(self.params);
                let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;

                // The field projection function expects the generics of the
                // containing struct (not those of the field).
                let addr = (impure.ref_to_field_ref)(self.addr, self.param_exprs, self.const_exprs);
                let snap = pure.read.call()(self.snap.downcast_ty());
                Ok(ImSets {
                    inner: inner.get_all_inner(addr, snap),
                    object: inner.get_all_object(addr, snap, self.inner_map),
                })
            })
            .reduce(|acc, e| {
                let a: ImSets = acc?;
                let b: ImSets = e?;
                Ok(ImSets {
                    inner: set_union(vcx, a.inner, b.inner),
                    object: set_union(vcx, a.object, b.object),
                })
            })
            .unwrap_or_else(|| Ok(self.empty_sets()))
    }

    fn all_in_enum(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<ImSets<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let discr_snap = data.1.0.snap_to_discr_snap.call()(self.snap.downcast_ty());
        let vcx = self.vcx;
        let folded = data
            .variants
            .iter()
            .map(|variant| {
                let inner = self.all_in_struct(&variant.inner)?;
                Ok((self.vcx.mk_eq_expr(discr_snap, variant.1.0.discr), inner))
            })
            .reduce(|acc, e| {
                let (cond, sets) = acc?;
                let (next_cond, next_sets): (_, ImSets) = e?;
                Ok((
                    next_cond,
                    ImSets {
                        inner: vcx.mk_ternary_expr(cond, sets.inner, next_sets.inner),
                        object: vcx.mk_ternary_expr(cond, sets.object, next_sets.object),
                    },
                ))
            });
        match folded {
            Some(sets) => Ok(sets?.1),
            // An uninhabited enum (e.g. `Never`) has no values and therefore
            // no interior-mutable objects.
            None => Ok(self.empty_sets()),
        }
    }
}

struct RawPtrToRefEnc;

impl TaskEncoder for RawPtrToRefEnc {
    task_encoder::encoder_cache!(RawPtrToRefEnc);
    const ENCODER_NAME: &'static str = "raw pointer to reference encoder";
    type TaskDescription<'vir> = ty::Mutability;
    type OutputFullDependency<'vir> = vir::FunctionIdn<'vir, vir::CSnap, vir::Ref>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        vir::with_vcx(|vcx| {
            let raw_ptr = vcx
                .tcx()
                .mk_ty_from_kind(ty::TyKind::RawPtr(vcx.tcx().types.self_param, *task_key));
            // Decompose in the context of the generic `Param` type, which
            // declares the single type parameter the pointee refers to.
            let raw_ptr = RustTyDecomposition::from_ty(raw_ptr, RustTyDecomposition::param().params);
            let raw_ptr = deps
                .require_ref::<TyPureEnc>(raw_ptr.ty)?
                .snapshot
                .downcast_ty::<vir::CSnap>();
            let fn_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "C_{}_ptr_to_ref", task_key.ptr_str()),
                raw_ptr,
                vir::TYPE_REF,
            );
            let func = vcx.mk_function(
                fn_idn,
                (vcx.mk_local_decl("ptr", raw_ptr),),
                &[],
                &[],
                None,
                None,
            );
            Ok((func, fn_idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for func in Self::all_outputs_local_no_errors(program) {
            program.add_function(func);
        }
    }
}

/// The abstract function materializing an inner-IM QP into its `Map` snapshot.
/// `qp_to_map(s)` requires write permission to `p_Param` for every element of
/// `s`, and its postcondition axiomatises the result: for each `im` in `s`,
/// `result[im]` is the generic snapshot of the object at `im`'s address.
pub(crate) struct QpToMapEnc;

pub(crate) type QpToMapFn<'vir> = vir::FunctionIdn<'vir, vir::Set, vir::Map>;

impl TaskEncoder for QpToMapEnc {
    task_encoder::encoder_cache!(QpToMapEnc);
    const ENCODER_NAME: &'static str = "interior mutability qp-to-map encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = QpToMapFn<'vir>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let pair = deps
            .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
            .unwrap();
        // The generic `Param` predicate and its snapshot function.
        let param = RustTyDecomposition::param();
        let param_ref = deps.require_dep::<TyImpureEnc>(param)?;
        let generic_pred = param_ref.data.ref_to_pred;
        let generic_snap = param_ref.data.ref_to_snap;

        vir::with_vcx(|vcx| {
            let set_ty = vcx.mk_ty_set(pair.ty);
            let map_ty = vcx.mk_ty_map(pair.ty, vir::TYPE_PSNAP);
            let idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "qp_to_map"),
                set_ty,
                map_ty,
            );
            deps.emit_output_ref((), ())?;

            let s = vcx.mk_local_decl("s", set_ty);
            let s_ex = vcx.mk_local_ex(s);
            let im = vcx.mk_local_decl("im", pair.ty);
            let im_ex = vcx.mk_local_ex(im);
            let addr = pair.destructors[0].call()(im_ex).downcast_ty::<vir::Ref>();
            let tyval = pair.destructors[1].call()(im_ex).downcast_ty::<vir::TyVal>();
            let in_s = vcx.mk_set_in_expr(im_ex, s_ex);

            // requires: forall im :: { im in s } im in s ==> acc(p_Param(addr, tyval), write)
            let pred = vcx.mk_predicate_app_expr(generic_pred(addr, &[tyval], &[])(None));
            let pre = vcx.mk_forall_expr(
                vcx.alloc_slice(&[im]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_s])]),
                vcx.mk_bin_op_expr(vir::BinOpKind::Implies, in_s, pred)
                    .downcast_ty(),
            );

            // ensures: forall im :: { im in s } im in s ==>
            //   (im in result && result[im] == p_Param_snap(addr, tyval))
            // The `im in result` conjunct makes the `result[im]` lookup
            // well-formed (Viper requires the key to be in the map's domain).
            let result_map: vir::ExprMap<'vir> = vcx.mk_result(map_ty);
            let contains = vcx.mk_map_contains_expr(result_map, im_ex);
            let lookup: vir::ExprPSnap<'vir> =
                vcx.mk_map_lookup_expr(result_map, im_ex).downcast_ty();
            let snap_at = generic_snap.call()(addr, &[tyval], &[]).downcast_ty::<vir::PSnap>();
            let entry = vcx.mk_conj(&[contains, vcx.mk_eq_expr(lookup, snap_at)]);
            let post = vcx.mk_forall_expr(
                vcx.alloc_slice(&[im]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_s])]),
                vcx.mk_bin_op_expr(vir::BinOpKind::Implies, in_s, entry)
                    .downcast_ty(),
            );

            let func = vcx.mk_function(
                idn,
                (s,),
                vcx.alloc_slice(&[pre]),
                vcx.alloc_slice(&[post]),
                None,
                None,
            );
            Ok((func, idn))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for func in Self::all_outputs_local_no_errors(program) {
            program.add_function(func);
        }
    }
}
