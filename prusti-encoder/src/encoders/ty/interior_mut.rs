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

/// The number of interior-mutability levels. Level 0 collects the
/// `#[pure] #[interior_mut]` accessors (whose permission expressions cannot
/// read interior-mutable state); level 1 collects the
/// `#[pure_unstable(true)] #[interior_mut]` accessors (whose permission
/// expressions may read level-0 state through the level-0 IM-QP `Map`
/// snapshot).
pub const IM_LEVELS: usize = 2;

/// The common Viper types of the interior-mutability encoding.
#[derive(Clone)]
pub(crate) struct ImTys<'vir> {
    /// The `Pair2[Ref, Type]` key identifying an interior-mutable object.
    pub(crate) key: PairUse<'vir>,
    /// `Map[Pair2[Ref, Type], Perm]`: a permission map, the components of the
    /// `_IM_N` results.
    pub(crate) perm_map: vir::TypeMap<'vir>,
    /// `Map[Pair2[Ref, Type], s_Param]`: a snapshot map (the materialized
    /// state of an IM QP, built by `qp_to_map`).
    pub(crate) snap_map: vir::TypeMap<'vir>,
    /// The `Pair2[Map[..], Map[..]]` result of the `_IM_N` functions: the
    /// first component holds the objects reachable behind owned places or
    /// `&mut`, the second those reachable behind `&`.
    pub(crate) result: PairUse<'vir>,
}

impl<'vir> ImTys<'vir> {
    pub(crate) fn new<E: TaskEncoder>(
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    ) -> Self {
        let key = deps
            .require_dep::<PairUseEnc>(vec![vir::TYPE_REF.as_dyn(), vir::TYPE_TYVAL.as_dyn()])
            .unwrap();
        let (perm_map, snap_map) = vir::with_vcx(|vcx| {
            (
                vcx.mk_ty_map(key.ty, vir::TYPE_PERM),
                vcx.mk_ty_map(key.ty, vir::TYPE_PSNAP),
            )
        });
        let result = deps
            .require_dep::<PairUseEnc>(vec![perm_map.as_dyn(), perm_map.as_dyn()])
            .unwrap();
        ImTys {
            key,
            perm_map,
            snap_map,
            result,
        }
    }

    /// Splits an `_IM_N` result into its `(owned, shared)` permission maps.
    pub(crate) fn split<Curr: 'vir, Next: 'vir>(
        &self,
        pair: vir::ExprGen<'vir, Curr, Next, vir::Pair>,
    ) -> (
        vir::ExprGenMap<'vir, Curr, Next>,
        vir::ExprGenMap<'vir, Curr, Next>,
    ) {
        (
            self.result.destructors[0].call()(pair).downcast_ty(),
            self.result.destructors[1].call()(pair).downcast_ty(),
        )
    }

    /// Constructs an `_IM_N` result from its `(owned, shared)` permission maps.
    pub(crate) fn cons<Curr: 'vir, Next: 'vir>(
        &self,
        owned: vir::ExprGenMap<'vir, Curr, Next>,
        shared: vir::ExprGenMap<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
        self.result.constructor.call()(&[owned.as_dyn(), shared.as_dyn()])
    }

    pub(crate) fn empty_map<Curr: 'vir, Next: 'vir>(&self) -> vir::ExprGenMap<'vir, Curr, Next> {
        vir::with_vcx(|vcx| vcx.mk_map_empty_expr(self.key.ty, vir::TYPE_PERM))
    }
}

/// The Viper `write` permission amount (`1/1`).
fn write_perm<'vir, Curr: 'vir, Next: 'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
) -> vir::ExprGen<'vir, Curr, Next, vir::Perm> {
    vcx.mk_bin_op_expr(
        vir::BinOpKind::FracPerm,
        vcx.mk_const_expr(vir::ConstData::Int(1)),
        vcx.mk_const_expr(vir::ConstData::Int(1)),
    )
    .downcast_ty()
}

/// The Viper `none` permission amount (`0/1`).
fn no_perm<'vir, Curr: 'vir, Next: 'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
) -> vir::ExprGen<'vir, Curr, Next, vir::Perm> {
    vcx.mk_bin_op_expr(
        vir::BinOpKind::FracPerm,
        vcx.mk_const_expr(vir::ConstData::Int(0)),
        vcx.mk_const_expr(vir::ConstData::Int(1)),
    )
    .downcast_ty()
}

/// The IM level of an `#[interior_mut]` accessor: 0 for `#[pure]`, 1 for
/// `#[pure_unstable(true)]`. Any other marking is rejected at collection.
fn accessor_level(def_id: DefId) -> usize {
    match crate::encoders::get_pure_unstable(def_id) {
        None => 0,
        Some(true) => 1,
        Some(false) => unreachable!("rejected at spec collection"),
    }
}

#[derive(Debug, Clone, Copy)]
pub struct TyInteriorMutUseExpr<'vir> {
    /// `s_Ty_IM_0`: the `(owned, shared)` permission maps of the level-0
    /// interior-mutable objects (from `#[pure] #[interior_mut]` accessors,
    /// e.g. `Cell`/`UnsafeCell`), reachable at any nesting depth.
    l0: InteriorMutFn0<'vir>,
    /// `s_Ty_IM_1`: the `(owned, shared)` permission maps of the level-1
    /// interior-mutable objects (from `#[pure_unstable(true)] #[interior_mut]`
    /// accessors, e.g. `RefCell`). Takes the level-0 IM-QP `Map` snapshot as
    /// an extra argument so its permission expressions can read level-0 state.
    l1: InteriorMutFn1<'vir>,
    args: GArgsTy<'vir>,
}

impl<'vir> TyInteriorMutUseExpr<'vir> {
    /// The level-0 `(owned, shared)` permission maps reachable from
    /// `addr`/`snap`.
    pub fn get_0<Curr: 'vir, Next: 'vir>(
        &self,
        addr: vir::ExprGenRef<'vir, Curr, Next>,
        snap: vir::ExprGenSnap<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
        self.l0.call()(addr, snap, self.args.get_ty(), self.args.get_const())
    }

    /// The level-1 `(owned, shared)` permission maps reachable from
    /// `addr`/`snap`. `im0_map` is the level-0 IM-QP `Map` snapshot.
    pub fn get_1<Curr: 'vir, Next: 'vir>(
        &self,
        addr: vir::ExprGenRef<'vir, Curr, Next>,
        snap: vir::ExprGenSnap<'vir, Curr, Next>,
        im0_map: vir::ExprGenMap<'vir, Curr, Next>,
    ) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
        self.l1.call()(
            addr,
            snap,
            im0_map,
            self.args.get_ty(),
            self.args.get_const(),
        )
    }

    /// The level-`level` pair; `im0_map` is required for level 1.
    pub fn get_level<Curr: 'vir, Next: 'vir>(
        &self,
        level: usize,
        addr: vir::ExprGenRef<'vir, Curr, Next>,
        snap: vir::ExprGenSnap<'vir, Curr, Next>,
        im0_map: Option<vir::ExprGenMap<'vir, Curr, Next>>,
    ) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
        match level {
            0 => self.get_0(addr, snap),
            1 => self.get_1(addr, snap, im0_map.unwrap()),
            _ => unreachable!(),
        }
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
                l0: r.l0,
                l1: r.l1,
                args,
            },
        ))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        TyInteriorMutEnc::emit_outputs(program);
        QpToMapEnc::emit_outputs(program);
        MapUnionEnc::emit_outputs(program);
        super::generics::interior_mut::InteriorMutGenericsEnc::emit_outputs(program);
    }
}

/// The fixed name of the IM-QP `Map` snapshot parameter threaded into
/// `#[pure_unstable]` functions' Viper encoding (the level-0 map for
/// `#[pure_unstable(true)]`, the combined level-0/level-1 map otherwise).
pub const PURE_UNSTABLE_IM_MAP: &str = "im_map";

/// The type of the IM-QP snapshot `Map[Pair2[Ref, Type], s_Param]` that
/// `#[pure_unstable]` functions take as an extra Viper argument.
pub fn pure_unstable_map_ty<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
) -> Result<vir::TypeMap<'vir>, EncodeFullError<'vir, E>> {
    Ok(ImTys::new(deps).snap_map)
}

/// The `LocalDecl` for the IM-QP `Map` parameter of a `#[pure_unstable]`
/// function. Built with a fixed name so the function signature ([`FunctionEnc`])
/// and the body encoding ([`MirPureEnc`], which forwards it to nested
/// `#[pure_unstable]` callees) agree on it.
pub fn pure_unstable_map_decl<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
) -> Result<vir::LocalDeclMap<'vir>, EncodeFullError<'vir, E>> {
    let ty = pure_unstable_map_ty(deps)?;
    Ok(vir::with_vcx(|vcx| vcx.mk_local_decl(PURE_UNSTABLE_IM_MAP, ty)))
}

/// Folds the components of several `(owned, shared)` pairs: the owned maps
/// are unioned with (assumed) disjoint domains, the shared maps with (assumed)
/// agreeing overlaps.
fn fold_components<'vir, Curr: 'vir, Next: 'vir>(
    tys: &ImTys<'vir>,
    unions: &MapUnionFns<'vir>,
    pairs: impl IntoIterator<Item = vir::ExprGen<'vir, Curr, Next, vir::Pair>>,
) -> (
    Option<vir::ExprGenMap<'vir, Curr, Next>>,
    Option<vir::ExprGenMap<'vir, Curr, Next>>,
) {
    let mut owned: Option<vir::ExprGenMap<'vir, Curr, Next>> = None;
    let mut shared: Option<vir::ExprGenMap<'vir, Curr, Next>> = None;
    for pair in pairs {
        let (o, s) = tys.split(pair);
        owned = Some(match owned {
            Some(acc) => unions.disjoint.call()(acc, o),
            None => o,
        });
        shared = Some(match shared {
            Some(acc) => unions.shared.call()(acc, s),
            None => s,
        });
    }
    (owned, shared)
}

/// Folds several `(owned, shared)` pairs component-wise (see
/// [`fold_components`]) into a single pair.
pub(crate) fn fold_pairs<'vir, Curr: 'vir, Next: 'vir>(
    tys: &ImTys<'vir>,
    unions: &MapUnionFns<'vir>,
    pairs: impl IntoIterator<Item = vir::ExprGen<'vir, Curr, Next, vir::Pair>>,
) -> vir::ExprGen<'vir, Curr, Next, vir::Pair> {
    let (owned, shared) = fold_components(tys, unions, pairs);
    tys.cons(
        owned.unwrap_or_else(|| tys.empty_map()),
        shared.unwrap_or_else(|| tys.empty_map()),
    )
}

/// Merges the `(owned, shared)` permission-map pairs of several sources into a
/// single map: the components are folded (see [`fold_components`]) and finally
/// the two sides are unioned disjointly (an owned object cannot also be behind
/// a `&`).
pub(crate) fn merge_pairs<'vir, Curr: 'vir, Next: 'vir>(
    tys: &ImTys<'vir>,
    unions: &MapUnionFns<'vir>,
    pairs: impl IntoIterator<Item = vir::ExprGen<'vir, Curr, Next, vir::Pair>>,
) -> vir::ExprGenMap<'vir, Curr, Next> {
    match fold_components(tys, unions, pairs) {
        (Some(o), Some(s)) => unions.disjoint.call()(o, s),
        (None, None) => tys.empty_map(),
        _ => unreachable!(),
    }
}

/// The quantified permission over an IM permission map:
/// `forall k :: { k in domain(m) } k in domain(m) ==> acc(p_Param(k._2_0, k._2_1), m[k])`.
pub fn im_quant_perm<'vir, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    map: vir::ExprMap<'vir>,
) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
    let tys = ImTys::new(deps);
    // The map keys are `(address, type)` pairs of unknown (dynamic) type, so
    // the permission for each is to the generic (`Param`) predicate.
    let generic_pred = deps
        .require_dep::<TyImpureEnc>(RustTyDecomposition::param())?
        .data
        .ref_to_pred;
    let k = vcx.mk_local_decl("im", tys.key.ty);
    let k_ex = vcx.mk_local_ex(k);
    let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(map));
    let amount = vcx.mk_map_lookup_expr(map, k_ex).downcast_ty::<vir::Perm>();
    let perm = vcx.mk_predicate_app_expr(generic_pred(
        tys.key.destructors[0].call()(k_ex).downcast_ty::<vir::Ref>(),
        &[tys.key.destructors[1].call()(k_ex).downcast_ty::<vir::TyVal>()],
        &[],
    )(Some(amount)));
    let body = vcx
        .mk_bin_op_expr(vir::BinOpKind::Implies, in_dom, perm)
        .downcast_ty();
    Ok(vcx.mk_forall_expr(
        vcx.alloc_slice(&[k]),
        vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
        body,
    ))
}

/// The IM-QP `Map` snapshot argument for a call to a `#[pure_unstable]`
/// function from a context that does not itself carry the map: an impure body,
/// or a spec/assertion of an impure method. There the heap is available at the
/// position the expression lands in, so the map is materialized on the spot
/// via `qp_to_map` over the merged permission maps of the callee arguments
/// (the same maps the enclosing method's boundary QPs range over, so
/// `qp_to_map`'s precondition is dischargeable from the held QP).
///
/// `inner_only` is the callee's `#[pure_unstable(..)]` flag: `true` passes the
/// level-0 map only, `false` the combined level-0/level-1 map.
///
/// `args` provides, per callee argument, its type decomposition, an address
/// expression, and its snapshot. The address may be a dummy (`null`) for
/// reference arguments: their `_IM_N` functions read through the snapshot's
/// deref address and ignore the top-level address parameter.
pub(crate) fn pure_unstable_call_map<'vir, Curr: 'vir, Next: 'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    args: &[(
        RustTyDecomposition<'vir>,
        vir::ExprGenRef<'vir, Curr, Next>,
        vir::ExprGenSnap<'vir, Curr, Next>,
    )],
    inner_only: bool,
) -> Result<vir::ExprGenMap<'vir, Curr, Next>, EncodeFullError<'vir, E>> {
    let tys = ImTys::new(deps);
    let unions = deps.require_dep::<MapUnionEnc>(())?;
    let qp_to_map = deps.require_dep::<QpToMapEnc>(())?;
    let mut ims = Vec::with_capacity(args.len());
    for (ty, addr, snap) in args {
        ims.push((deps.require_dep::<TyInteriorMutUseEnc>(*ty)?, *addr, *snap));
    }
    vir::with_vcx(|_vcx| {
        let m0 = merge_pairs(
            &tys,
            &unions,
            ims.iter().map(|(im, addr, snap)| im.get_0(*addr, *snap)),
        );
        let m = if inner_only {
            m0
        } else {
            // TODO: `qp_to_map` only yields snapshots for positive-permission
            // entries; a level-1 object held with `none` permission has no
            // readable snapshot in the combined map.
            let l0_map = qp_to_map.call()(m0);
            let m1 = merge_pairs(
                &tys,
                &unions,
                ims.iter()
                    .map(|(im, addr, snap)| im.get_1(*addr, *snap, l0_map)),
            );
            unions.disjoint.call()(m0, m1)
        };
        Ok(qp_to_map.call()(m))
    })
}

pub(super) struct TyInteriorMutEnc;

pub(crate) type InteriorMutFn0<'vir> =
    vir::FunctionIdn<'vir, (vir::Ref, vir::Snap, vir::ManyTyVal, vir::ManyCSnap), vir::Pair>;

/// The level-1 function additionally takes the level-0 IM-QP `Map` snapshot
/// (`Map[Pair2[Ref, Type], s_Param]`), so that its permission expressions can
/// read level-0 interior-mutable state (e.g. a `RefCell`'s borrow count)
/// through it.
pub(crate) type InteriorMutFn1<'vir> = vir::FunctionIdn<
    'vir,
    (vir::Ref, vir::Snap, vir::Map, vir::ManyTyVal, vir::ManyCSnap),
    vir::Pair,
>;

#[derive(Debug, Clone, Copy)]
pub(super) struct TyInteriorMutRef<'vir> {
    pub(super) l0: InteriorMutFn0<'vir>,
    pub(super) l1: InteriorMutFn1<'vir>,
}

impl<'vir> OutputRefAny for TyInteriorMutRef<'vir> {}

/// The `(owned, shared)` permission maps of one level of a type's
/// interior-mutable objects: `owned` holds the objects reachable behind owned
/// places or `&mut`, `shared` those reachable behind `&`.
#[derive(Clone, Copy)]
struct ImPair<'vir> {
    owned: vir::ExprMap<'vir>,
    shared: vir::ExprMap<'vir>,
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
            let tys = ImTys::new(deps);
            let unions = deps.require_dep::<MapUnionEnc>(())?;
            let pure = deps.require_dep::<TyPureEnc>(*task_key)?;
            let impure = deps.require_dep::<TyImpureEnc>(*task_key)?;
            let params = deps
                .require_dep::<GenericParamsEnc>(task_key.params)
                .unwrap();
            let addr = vcx.mk_local_decl("addr", vir::TYPE_REF);
            let snap = vcx.mk_local_decl("snap", pure.snapshot);
            // The level-0 IM-QP `Map` snapshot, passed to the level-1 function.
            let im0_map = vcx.mk_local_decl("im_0_map", tys.snap_map);
            let l0_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{}_IM_0", task_key.name.as_str()),
                (addr.ty, snap.ty, params.ty_args(), params.const_args()),
                tys.result.ty,
            );
            let l1_idn = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "s_{}_IM_1", task_key.name.as_str()),
                (
                    addr.ty,
                    snap.ty,
                    im0_map.ty,
                    params.ty_args(),
                    params.const_args(),
                ),
                tys.result.ty,
            );
            deps.emit_output_ref(
                *task_key,
                TyInteriorMutRef {
                    l0: l0_idn,
                    l1: l1_idn,
                },
            )?;

            let addr_ex = vcx.mk_local_ex(addr);
            let snap_ex = vcx.mk_local_ex(snap);
            let im0_map_ex = vcx.mk_local_ex(im0_map);

            // The two levels are structurally identical; level 1 additionally
            // has the `im_0_map` parameter, threaded to its (level-1) accessors
            // and their permission expressions.
            let encode_level = |deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
                                    level: usize|
             -> Result<_, EncodeFullError<'vir, Self>> {
                let snap_map = (level == 1).then_some(im0_map_ex);
                let mut field_enc = TyInteriorMutField {
                    vcx,
                    tys: tys.clone(),
                    unions,
                    deps,
                    params: task_key.params,
                    param_exprs: params.ty_exprs(),
                    const_exprs: params.const_exprs(),
                    addr: addr_ex,
                    snap: snap_ex,
                    level,
                    snap_map,
                };
                // The recursive (field/ref) contributions.
                let body: Option<ImPair> = match &task_key.zip(vcx.alloc(pure.zip(impure))).specifics
                {
                    _ if task_key.unsafe_cell => Some(field_enc.empty_pair()),
                    TySpecifics::Primitive(_) => Some(field_enc.empty_pair()),
                    // A raw pointer gives no permission to its pointee, so it
                    // contributes no interior-mutable objects.
                    TySpecifics::Raw(_) => Some(field_enc.empty_pair()),
                    TySpecifics::Param(_) => None,
                    TySpecifics::Opaque(_) => None,
                    TySpecifics::ImmRef(data) => Some(field_enc.all_in_immref(data)?),
                    TySpecifics::MutRef(data) => Some(field_enc.all_in_mutref(data)?),
                    // Builtins (e.g. `Real`) have no interior-mutable objects.
                    TySpecifics::Builtin(_) => Some(field_enc.empty_pair()),
                    TySpecifics::ArrayLike(_) => todo!(),
                    TySpecifics::StructLike(data) => Some(field_enc.all_in_struct(data)?),
                    TySpecifics::EnumLike(enum_data) => Some(field_enc.all_in_enum(enum_data)?),
                };
                // This type's own accessors of this level (e.g. the `*mut T`
                // of a `Cell` at level 0, of a `RefCell` at level 1). Own
                // objects live in the value itself, so they belong to the
                // owned map.
                let mut own: vir::ExprMap<'vir> = field_enc.tys.empty_map();
                let mut has_own = false;
                for im in task_key.interior_mut.iter() {
                    if accessor_level(*im) != level {
                        continue;
                    }
                    let (key, perm) = field_enc.own_object(*im, task_key, addr_ex, snap_ex)?;
                    own = vcx.mk_map_update_expr(own, key, perm);
                    has_own = true;
                }
                assert!(body.is_some() || !has_own);
                let combined = body.map(|b| ImPair {
                    owned: if has_own {
                        field_enc.unions.disjoint.call()(b.owned, own)
                    } else {
                        b.owned
                    },
                    shared: b.shared,
                });

                let result: vir::Expr<'vir, vir::Pair> = vcx.mk_result(tys.result.ty);
                let mut posts = combined
                    .map(|p| vcx.mk_eq_expr(result, tys.cons(p.owned, p.shared)))
                    .into_iter()
                    .collect::<Vec<_>>();
                // The (assumed) nonnegativity of all permission amounts: QPs
                // over these maps need their amounts to be provably
                // nonnegative. Added unconditionally (also for the abstract
                // `s_Param_IM_N`): the functions have no body, so the
                // postcondition is taken as an axiom.
                let (owned_res, shared_res) = tys.split(result);
                posts.push(nonneg_post(vcx, &tys, owned_res));
                posts.push(nonneg_post(vcx, &tys, shared_res));
                Ok(posts)
            };

            let l0_posts = encode_level(deps, 0)?;
            let l0_fn = vcx.mk_function(
                l0_idn,
                (addr, snap, params.ty_decls(), params.const_decls()),
                &[],
                vcx.alloc_slice(&l0_posts),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            let l1_posts = encode_level(deps, 1)?;
            let l1_fn = vcx.mk_function(
                l1_idn,
                (
                    addr,
                    snap,
                    im0_map,
                    params.ty_decls(),
                    params.const_decls(),
                ),
                &[],
                vcx.alloc_slice(&l1_posts),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            Ok((vec![l0_fn, l1_fn], ()))
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

/// The (assumed) nonnegativity postcondition for one component map of an
/// `_IM_N` result: every entry's permission amount is nonnegative.
fn nonneg_post<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    tys: &ImTys<'vir>,
    map: vir::ExprMap<'vir>,
) -> vir::ExprBool<'vir> {
    let k = vcx.mk_local_decl("im", tys.key.ty);
    let k_ex = vcx.mk_local_ex(k);
    let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(map));
    let amount = vcx.mk_map_lookup_expr(map, k_ex).downcast_ty::<vir::Perm>();
    let nonneg = vcx
        .mk_bin_op_expr(vir::BinOpKind::PermGeCmp, amount, no_perm(vcx))
        .downcast_ty();
    let body = vcx
        .mk_bin_op_expr(vir::BinOpKind::Implies, in_dom, nonneg)
        .downcast_ty();
    vcx.mk_forall_expr(
        vcx.alloc_slice(&[k]),
        vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
        body,
    )
}

struct TyInteriorMutField<'a, 'vir> {
    vcx: &'vir vir::VirCtxt<'vir>,
    tys: ImTys<'vir>,
    unions: MapUnionFns<'vir>,
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyInteriorMutEnc>,
    params: GParams<'vir>,
    param_exprs: &'a [vir::ExprTyVal<'vir>],
    const_exprs: &'a [vir::ExprCSnap<'vir>],
    addr: vir::ExprRef<'vir>,
    snap: vir::ExprSnap<'vir>,
    /// The level being encoded (0 or 1).
    level: usize,
    /// The level-0 IM-QP `Map` snapshot parameter of the level-1 function
    /// being built (`None` at level 0), passed down to nested level-1
    /// functions and permission expressions.
    snap_map: Option<vir::ExprMap<'vir>>,
}

impl<'vir> TyInteriorMutField<'_, 'vir> {
    fn empty_pair(&self) -> ImPair<'vir> {
        ImPair {
            owned: self.tys.empty_map(),
            shared: self.tys.empty_map(),
        }
    }

    /// The `(key, perm)` map entry for one of the type's own `#[interior_mut]`
    /// accessors: the key is `(accessor(self), type)`, the permission the
    /// evaluated `#[interior_mut(EXPR)]` expression (or `write` without one).
    fn own_object(
        &mut self,
        im: DefId,
        task_key: &RustTy<'vir>,
        addr_ex: vir::ExprRef<'vir>,
        snap_ex: vir::ExprSnap<'vir>,
    ) -> Result<
        (vir::Expr<'vir, vir::Pair>, vir::ExprPerm<'vir>),
        EncodeFullError<'vir, TyInteriorMutEnc>,
    > {
        let vcx = self.vcx;
        let call = CallTaskDescription::new(
            task_key.data.params,
            task_key.data.params.rust_params(),
            im,
        );
        let signature = vcx.tcx().fn_sig(im).skip_binder();
        let input = signature.inputs().skip_binder()[0];
        let input = RustTyDecomposition::from_ty(input, task_key.data.params);
        let metadata_ty = input
            .ty
            .ref_data()
            .unwrap()
            .metadata
            .decompose_normalize(input.args);
        let metadata = match self
            .deps
            .require_dep::<TyUsePureEnc>(metadata_ty)
            .unwrap()
            .zst_to_snap()
        {
            Some(m) => m.upcast_ty(),
            // The receiver is not statically thin (e.g. the accessor is on
            // `impl<T: ?Sized>`). The metadata value is irrelevant for the
            // accessor call, so use the arbitrary (but deterministic) snapshot
            // to keep the maps consistent across states.
            None => self
                .deps
                .require_ref::<TyUsePureEnc>(metadata_ty)
                .unwrap()
                .arbitrary_to_snap(),
        };
        let input = self
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
        let accessor = self.deps.require_dep::<FunctionCallEnc>(call).unwrap();
        let args = vec![input.upcast_ty()];
        // A level-1 accessor is `#[pure_unstable(true)]`, so its Viper
        // function takes the level-0 map.
        let result = if accessor.is_pure_unstable() {
            accessor.call_pure_unstable(args, self.snap_map.unwrap())
        } else {
            accessor.call_pure(args)
        };
        let raw_ptr_to_ref = self.deps.require_dep::<RawPtrToRefEnc>(mut_).unwrap();
        let ref_ = raw_ptr_to_ref(result.downcast_ty());
        let ty_ = RustTyDecomposition::from_ty(inner, task_key.data.params);
        let ty_expr = ty_identity_expr(self.deps, ty_);
        let key = (self.tys.key.constructor)(&[ref_.as_dyn(), ty_expr.as_dyn()]);
        let perm = match crate::encoders::get_interior_mut_perm(im) {
            Some(perm_def_id) => self.eval_perm(perm_def_id, input, task_key.data.params)?,
            None => write_perm(vcx),
        };
        Ok((key, perm))
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
        let perm_func = self.deps.require_dep::<FunctionCallEnc>(call).unwrap();
        let args = vec![input.upcast_ty()];
        // A level-1 permission closure is `#[pure_unstable(true)]`: it takes
        // the level-0 map (this level-1 function's `im_0_map` parameter) to
        // read level-0 interior-mutable state (e.g. a `RefCell`'s borrow
        // count). A level-0 permission closure is plain pure.
        let perm_snap = if perm_func.is_pure_unstable() {
            perm_func.call_pure_unstable(args, self.snap_map.unwrap())
        } else {
            perm_func.call_pure(args)
        };
        // `Real` is represented natively as Viper `Perm`, so the returned
        // snapshot is the permission amount directly.
        Ok(perm_snap.downcast_ty())
    }

    /// The pair of the referent of a reference field/type, computed from the
    /// referent value in the reference's snapshot.
    fn referent_pair(
        &mut self,
        referent: RustTyDecomposition<'vir>,
        addr: vir::ExprRef<'vir>,
        snap: vir::ExprSnap<'vir>,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(referent)?;
        let pair = inner.get_level(self.level, addr, snap, self.snap_map);
        let (owned, shared) = self.tys.split(pair);
        Ok(ImPair { owned, shared })
    }

    /// A mutable reference grants all interior-mutable objects reachable
    /// through it, preserving the owned/shared split of the referent.
    fn all_in_mutref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::MutRefData,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let addr = pure.deref_access.call()(self.snap.downcast_ty());
        let snap = pure.value_access.call()(self.snap.downcast_ty());
        self.referent_pair(ty, addr, snap.upcast_ty())
    }

    /// A shared reference collapses the referent's whole pair into the shared
    /// side: everything below it is only reachable behind a `&`.
    fn all_in_immref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::ImmRefData,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let addr = pure.deref_access.call()(self.snap.downcast_ty());
        let snap = pure.value_access.call()(self.snap.downcast_ty());
        let p = self.referent_pair(ty, addr, snap.upcast_ty())?;
        Ok(ImPair {
            owned: self.tys.empty_map(),
            shared: self.unions.disjoint.call()(p.owned, p.shared),
        })
    }

    fn all_in_struct(
        &mut self,
        data: &StructData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let mut result: Option<ImPair<'vir>> = None;
        for (field, (pure, impure)) in data.fields.iter() {
            let ty = field.decompose(self.params);
            // The field projection function expects the generics of the
            // containing struct (not those of the field).
            let addr = (impure.ref_to_field_ref)(self.addr, self.param_exprs, self.const_exprs);
            let snap = pure.read.call()(self.snap.downcast_ty());
            let inner = self.deps.require_dep::<TyInteriorMutUseEnc>(ty)?;
            let pair = inner.get_level(self.level, addr, snap, self.snap_map);
            let (owned, shared) = self.tys.split(pair);
            result = Some(match result {
                Some(acc) => ImPair {
                    owned: self.unions.disjoint.call()(acc.owned, owned),
                    shared: self.unions.shared.call()(acc.shared, shared),
                },
                None => ImPair { owned, shared },
            });
        }
        Ok(result.unwrap_or_else(|| self.empty_pair()))
    }

    fn all_in_enum(
        &mut self,
        data: &EnumData<'vir, (RustTyDatas, (PureTyDatas, ImpureTyDatas))>,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
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
                let (cond, pair) = acc?;
                let (next_cond, next_pair): (_, ImPair) = e?;
                Ok((
                    next_cond,
                    ImPair {
                        owned: vcx.mk_ternary_expr(cond, pair.owned, next_pair.owned),
                        shared: vcx.mk_ternary_expr(cond, pair.shared, next_pair.shared),
                    },
                ))
            });
        match folded {
            Some(pair) => Ok(pair?.1),
            // An uninhabited enum (e.g. `Never`) has no values and therefore
            // no interior-mutable objects.
            None => Ok(self.empty_pair()),
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
            let raw_ptr =
                RustTyDecomposition::from_ty(raw_ptr, RustTyDecomposition::param().params);
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

/// The custom-axiomatised union functions for IM permission maps.
pub(crate) struct MapUnionEnc;

pub(crate) type MapUnionFn<'vir> = vir::FunctionIdn<'vir, (vir::Map, vir::Map), vir::Map>;

#[derive(Debug, Clone, Copy)]
pub(crate) struct MapUnionFns<'vir> {
    /// Union of maps with (assumed) disjoint domains: used for owned maps
    /// (exclusive access implies distinct addresses) and for the final
    /// owned-with-shared merge (an owned object cannot also be behind a `&`).
    pub(crate) disjoint: MapUnionFn<'vir>,
    /// Union of maps whose overlapping keys are (assumed) to agree: used for
    /// shared maps, where the same object may be reachable through several
    /// aliasing `&`s, always with the same permission.
    pub(crate) shared: MapUnionFn<'vir>,
}

impl TaskEncoder for MapUnionEnc {
    task_encoder::encoder_cache!(MapUnionEnc);
    const ENCODER_NAME: &'static str = "interior mutability map union encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = MapUnionFns<'vir>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let tys = ImTys::new(deps);
        vir::with_vcx(|vcx| {
            let build = |name: &str, disjoint: bool| {
                let idn: MapUnionFn<'vir> = vir::FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "{name}"),
                    (tys.perm_map, tys.perm_map),
                    tys.perm_map,
                );
                let a = vcx.mk_local_decl("a", tys.perm_map);
                let b = vcx.mk_local_decl("b", tys.perm_map);
                let a_ex = vcx.mk_local_ex(a);
                let b_ex = vcx.mk_local_ex(b);
                let result: vir::ExprMap<'vir> = vcx.mk_result(tys.perm_map);
                let dom = |m| vcx.mk_map_domain_expr(m);
                // domain(result) == domain(a) union domain(b)
                let dom_post = vcx.mk_eq_expr(
                    dom(result),
                    vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, dom(a_ex), dom(b_ex))
                        .downcast_ty::<vir::Set>(),
                );
                // forall k :: { k in domain(m) } k in domain(m) ==> result[k] == m[k]
                let lookup_post = |m: vir::ExprMap<'vir>| {
                    let k = vcx.mk_local_decl("k", tys.key.ty);
                    let k_ex = vcx.mk_local_ex(k);
                    let in_dom = vcx.mk_set_in_expr(k_ex, dom(m));
                    let eq = vcx.mk_eq_expr(
                        vcx.mk_map_lookup_expr(result, k_ex).downcast_ty::<vir::Perm>(),
                        vcx.mk_map_lookup_expr(m, k_ex).downcast_ty::<vir::Perm>(),
                    );
                    let body = vcx
                        .mk_bin_op_expr(vir::BinOpKind::Implies, in_dom, eq)
                        .downcast_ty();
                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&[k]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                        body,
                    )
                };
                // The union of nonnegative maps is nonnegative; stated as an
                // (assumed) post like on the `_IM_N` functions, so QPs over
                // union results are well-formed.
                let mut posts = vec![
                    dom_post,
                    lookup_post(a_ex),
                    lookup_post(b_ex),
                    nonneg_post(vcx, &tys, result),
                ];
                if disjoint {
                    // The (assumed) domain disjointness:
                    // forall k :: { k in domain(a) } k in domain(a) ==> !(k in domain(b))
                    let k = vcx.mk_local_decl("k", tys.key.ty);
                    let k_ex = vcx.mk_local_ex(k);
                    let in_a = vcx.mk_set_in_expr(k_ex, dom(a_ex));
                    let not_in_b = vcx
                        .mk_unary_op_expr(
                            vir::UnOpKind::Not,
                            vcx.mk_set_in_expr(k_ex, dom(b_ex)).upcast_ty(),
                        )
                        .downcast_ty();
                    let body = vcx
                        .mk_bin_op_expr(vir::BinOpKind::Implies, in_a, not_in_b)
                        .downcast_ty();
                    posts.push(vcx.mk_forall_expr(
                        vcx.alloc_slice(&[k]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[in_a])]),
                        body,
                    ));
                }
                let func = vcx.mk_function(
                    idn,
                    (a, b),
                    &[],
                    vcx.alloc_slice(&posts),
                    None,
                    None,
                );
                (func, idn)
            };
            let (disjoint_fn, disjoint) = build("im_map_union_disjoint", true);
            let (shared_fn, shared) = build("im_map_union_shared", false);
            deps.emit_output_ref((), ())?;
            Ok((vec![disjoint_fn, shared_fn], MapUnionFns { disjoint, shared }))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for funcs in Self::all_outputs_local_no_errors(program) {
            for func in funcs {
                program.add_function(func);
            }
        }
    }
}

/// The abstract function materializing an IM QP into its `Map` snapshot.
/// `qp_to_map(m)` requires the permission the QP over `m` grants (which is how
/// applications are discharged from the held QP), and its postcondition
/// axiomatises the result: for each key with positive permission, the result
/// holds the generic snapshot of the object at that key's address.
pub(crate) struct QpToMapEnc;

pub(crate) type QpToMapFn<'vir> = vir::FunctionIdn<'vir, vir::Map, vir::Map>;

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
        let tys = ImTys::new(deps);
        // The generic `Param` predicate and its snapshot function.
        let param_ref = deps.require_dep::<TyImpureEnc>(RustTyDecomposition::param())?;
        let generic_pred = param_ref.data.ref_to_pred;
        let generic_snap = param_ref.data.ref_to_snap;

        vir::with_vcx(|vcx| {
            let idn: QpToMapFn<'vir> = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "qp_to_map"),
                tys.perm_map,
                tys.snap_map,
            );
            deps.emit_output_ref((), ())?;

            let m = vcx.mk_local_decl("m", tys.perm_map);
            let m_ex = vcx.mk_local_ex(m);
            let k = vcx.mk_local_decl("k", tys.key.ty);
            let k_ex = vcx.mk_local_ex(k);
            let addr = tys.key.destructors[0].call()(k_ex).downcast_ty::<vir::Ref>();
            let tyval = tys.key.destructors[1].call()(k_ex).downcast_ty::<vir::TyVal>();
            let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(m_ex));
            let amount = vcx.mk_map_lookup_expr(m_ex, k_ex).downcast_ty::<vir::Perm>();
            let amount_nonneg = vcx
                .mk_bin_op_expr(vir::BinOpKind::PermGeCmp, amount, no_perm(vcx))
                .downcast_ty();

            // requires: forall k :: { k in domain(m) }
            //   k in domain(m) && m[k] >= none ==> acc(p_Param(k._2_0, k._2_1), m[k])
            // (the nonnegativity conjunct makes the amount well-formed for an
            // arbitrary map; the maps this is applied to are nonnegative by
            // assumption).
            let pred = vcx.mk_predicate_app_expr(generic_pred(addr, &[tyval], &[])(Some(amount)));
            let pre = vcx.mk_forall_expr(
                vcx.alloc_slice(&[k]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::Implies,
                    vcx.mk_conj(&[in_dom, amount_nonneg]),
                    pred,
                )
                .downcast_ty(),
            );

            // ensures: domain(result) == domain(m)
            let result_map: vir::ExprMap<'vir> = vcx.mk_result(tys.snap_map);
            let dom_post = vcx.mk_eq_expr(
                vcx.mk_map_domain_expr(result_map),
                vcx.mk_map_domain_expr(m_ex),
            );
            // ensures: forall k :: { k in domain(m) }
            //   k in domain(m) && !(none >= m[k]) ==> result[k] == p_Param_snap(k._2_0, k._2_1)
            // (reading the snapshot needs a positive permission amount).
            let amount_pos = vcx
                .mk_unary_op_expr(
                    vir::UnOpKind::Not,
                    vcx.mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount),
                )
                .downcast_ty();
            let lookup: vir::ExprPSnap<'vir> =
                vcx.mk_map_lookup_expr(result_map, k_ex).downcast_ty();
            let snap_at = generic_snap.call()(addr, &[tyval], &[]).downcast_ty::<vir::PSnap>();
            let entry_post = vcx.mk_forall_expr(
                vcx.alloc_slice(&[k]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::Implies,
                    vcx.mk_conj(&[in_dom, amount_pos]),
                    vcx.mk_eq_expr(lookup, snap_at),
                )
                .downcast_ty(),
            );

            let func = vcx.mk_function(
                idn,
                (m,),
                vcx.alloc_slice(&[pre]),
                vcx.alloc_slice(&[dom_post, entry_post]),
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
