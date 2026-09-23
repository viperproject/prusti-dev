use prusti_rustc_interface::{middle::ty, span::def_id::DefId};
use task_encoder::{EncodeFullError, OutputRefAny, TaskEncoder};
use vir::CastType;

use crate::encoders::{
    FunctionCallEnc, Pure, TyUsePureEnc,
    custom::{PairUse, PairUseEnc},
    mir_fn::CallTaskDescription,
    ty::{
        LazyRustTy, RustTy, RustTyDatas, RustTyDecomposition, RustTyNormalized, RustTySpecial,
        data::{EnumData, StructData, TyDatas, TySpecifics},
        generics::{GArgsCastEnc, GArgsTy, GArgsTyEnc, GParams, GenericParams, GenericParamsEnc},
        impure::{ImpureTyDatas, TyImpureEnc},
        pure::{PureTyDatas, TyPureEnc},
    },
};

/// The type-value expression of `ty` in the context of its own arguments.
fn ty_identity_expr<'vir, T: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, T>,
    ty: RustTyDecomposition<'vir>,
) -> vir::ExprTyVal<'vir> {
    // The decomposition's arguments live in its context (which coincides
    // with the type's own parameters only for an identity decomposition).
    let params = deps
        .require_dep::<GenericParamsEnc>(ty.args.context())
        .unwrap();
    params.ty_expr(deps, ty).unwrap()
}

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
pub enum TyInteriorMutError {}

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
        MapRestrictEnc::emit_outputs(program);
        Im0SnapEnc::emit_outputs(program);
        Im0JoinEnc::emit_outputs(program);
        super::generics::interior_mut::InteriorMutGenericsEnc::emit_outputs(program);
    }
}

/// The fixed name of the IM-QP `Map` snapshot parameter threaded into
/// `#[pure_unstable]` functions' Viper encoding (the level-0 map for
/// `#[pure_unstable(true)]`, the combined level-0/level-1 map otherwise).
pub const PURE_UNSTABLE_IM_MAP: &str = "im_map";

/// The fixed name of the `let`-bound level-0 IM-QP `Map` snapshot in a method
/// contract's IM QP clause. The indirect (behind-reference) level-1 pair
/// expressions reference it as a free variable, so any context embedding them
/// must bind it around the level-1 QP (see `mk_qps` in the method encoder).
/// Materializing the map inline instead (a heap-dependent `qp_to_map`
/// application inside the QP's map terms) defeats Silicon's instantiation of
/// the union functions' postconditions.
pub const BOUNDARY_IM0_MAP: &str = "im0_map";

/// A free-variable reference to the [`BOUNDARY_IM0_MAP`] binding.
pub(crate) fn boundary_im0_map<'vir, Curr: 'vir, Next: 'vir>(
    tys: &ImTys<'vir>,
) -> vir::ExprGenMap<'vir, Curr, Next> {
    vir::with_vcx(|vcx| vcx.mk_local_ex(vcx.mk_local_decl(BOUNDARY_IM0_MAP, tys.snap_map)))
}

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
    Ok(vir::with_vcx(|vcx| {
        vcx.mk_local_decl(PURE_UNSTABLE_IM_MAP, ty)
    }))
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
    if inner_only {
        let unions = deps.require_dep::<MapUnionEnc>(())?;
        let restrict = deps.require_dep::<MapRestrictEnc>(())?.restrict;
        // The keys are phrased over the sources' triples, like the domain
        // of `im0_snap` itself: membership in them directly triggers its
        // value postconditions.
        let param_im = deps.require_ref::<TyInteriorMutEnc>(RustTyDecomposition::param())?;
        let mut m0: Option<vir::ExprGenMap<'vir, Curr, Next>> = None;
        for (ty, addr, snap) in args {
            let (r, s, t) = im0_source_triple(deps, *ty, *addr, *snap)?;
            let ts = vir::with_vcx(|vcx| vcx.alloc_slice(&[lift_ty_expr(t)]));
            let (o, sh) = tys.split(param_im.l0.call()(r, s.upcast_ty(), ts, &[]));
            let u = unions.disjoint.call()(o, sh);
            m0 = Some(match m0 {
                None => u,
                Some(m) => unions.shared.call()(m, u),
            });
        }
        let m0 = m0.unwrap_or_else(|| tys.empty_map());
        // The canonical `im0_snap` map of the arguments, restricted to the
        // level-0 keys reachable from them: the same term shape as the
        // applications inside the `_IM_1` bodies (see `eval_perm`), so the
        // `im_map_restrict` canonicity axiom equates them from pointwise
        // agreement.
        let im0 = im0_snap_sources(deps, args, &[])?;
        return vir::with_vcx(|vcx| Ok(restrict.call()(im0, vcx.mk_map_domain_expr(m0))));
    }
    // Level-0 and level-1 objects: per argument the join of its canonical
    // `im0_snap` and `im1_snap` maps (see `Im0SnapEnc`), the former bound
    // once for both uses.
    let im_snap = deps.require_dep::<Im0SnapEnc>(())?;
    let join = deps.require_dep::<Im0JoinEnc>(())?;
    let mut map = None;
    for (idx, (ty, addr, snap)) in args.iter().enumerate() {
        let (r, s, t) = im0_source_triple(deps, *ty, *addr, *snap)?;
        let app = vir::with_vcx(|vcx| {
            if provably_no_level1_interior_mut(*ty, &mut Default::default()) {
                return im_snap.full.call()(r, s, lift_ty_expr(t));
            }
            let im0_decl =
                vcx.mk_local_decl(vir::vir_format!(vcx, "im_values0_{idx}"), tys.snap_map);
            let im0 = vcx.mk_local_ex(im0_decl);
            let im1 = im_snap.level1.call()(r, s, im0, lift_ty_expr(t));
            vcx.mk_let_expr(
                im0_decl,
                im_snap.full.call()(r, s, lift_ty_expr(t)),
                join.call()(im0, im1),
            )
        });
        map = Some(match map {
            None => app,
            Some(m) => join.call()(m, app),
        });
    }
    Ok(map
        .unwrap_or_else(|| vir::with_vcx(|vcx| vcx.mk_map_empty_expr(tys.key.ty, vir::TYPE_PSNAP))))
}

/// The `im0_snap` argument triple `(r, s, T)` of one boundary source,
/// normalized so that both sides of a boundary produce literally the same
/// application (which is what makes the canonical function work: equal
/// arguments give equal applications by plain congruence, with no
/// map-extensionality reasoning). Reference-typed sources resolve to their
/// referent: their `_IM_N` functions ignore the top-level address (which
/// differs across a call boundary), reading through the deref address
/// embedded in the (equal) snapshots. Other sources use the address (the
/// callee receives the caller's operand `Ref`s) and the `Param`-cast
/// snapshot.
pub(crate) fn im0_source_triple<'vir, Curr: 'vir, Next: 'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    ty: RustTyDecomposition<'vir>,
    addr: vir::ExprGenRef<'vir, Curr, Next>,
    snap: vir::ExprGenSnap<'vir, Curr, Next>,
) -> Result<
    (
        vir::ExprGenRef<'vir, Curr, Next>,
        vir::ExprGenPSnap<'vir, Curr, Next>,
        vir::ExprTyVal<'vir>,
    ),
    EncodeFullError<'vir, E>,
> {
    let enc = deps.require_dep::<TyUsePureEnc>(ty)?;
    match &enc.specifics {
        TySpecifics::ImmRef(_) => {
            let referent = ty
                .ty
                .ref_data()
                .unwrap()
                .referent
                .decompose_normalize(ty.args);
            // Encode the referent type's IM functions (and with them its
            // `s_Param_IM_N` dispatch axioms), which the emitted generic
            // application depends on.
            deps.require_dep::<TyInteriorMutUseEnc>(referent)?;
            let data = enc.expect_immref();
            let r = data.addr_access(snap.downcast_ty());
            let s = data.value_access_generic(snap.downcast_ty());
            Ok((
                im_source_addr(referent, r),
                s,
                ty_identity_expr(deps, referent),
            ))
        }
        TySpecifics::MutRef(_) => {
            let referent = ty
                .ty
                .ref_data()
                .unwrap()
                .referent
                .decompose_normalize(ty.args);
            deps.require_dep::<TyInteriorMutUseEnc>(referent)?;
            let data = enc.expect_mutref();
            let r = data.deref_access(snap.downcast_ty());
            // A mutable reference's snapshot is shallow (it does not contain
            // the referent's value), so the value is read from the heap:
            // while the reference is live its referent is held in generic
            // (`p_Param`) form. The value matters for holders whose objects
            // are keyed by pointers STORED in the value (e.g. a `Ref` guard).
            let t = ty_identity_expr(deps, referent);
            let generic_snap = deps
                .require_dep::<TyImpureEnc>(RustTyDecomposition::param())?
                .data
                .ref_to_snap;
            let s = vir::with_vcx(|vcx| {
                generic_snap.call()(r, vcx.alloc_slice(&[lift_ty_expr(t)]), &[])
                    .downcast_ty::<vir::PSnap>()
            });
            Ok((im_source_addr(referent, r), s, t))
        }
        TySpecifics::Param(_) => Ok((addr, snap.downcast_ty(), ty_identity_expr(deps, ty))),
        _ => {
            deps.require_dep::<TyInteriorMutUseEnc>(ty)?;
            let s = cast_snap_to_param(deps, ty, snap)?;
            Ok((im_source_addr(ty, addr), s, ty_identity_expr(deps, ty)))
        }
    }
}

/// The level-0 and level-1 boundary QP maps of the given sources, phrased
/// over the same normalized triples as `im0_snap` (see `im0_source_triple`):
/// per source the flat union of the `s_Param_IM_N` pair components, merged
/// across sources with the shared union (aliasing sources reach the same
/// objects with the same amounts). Matching `im0_snap`'s precondition union
/// term-for-term makes its wildcard permission check against these QPs
/// (near-)syntactic; deriving it through the type-level `_IM_N` posts and
/// pair destructors instead is a chain Z3 only finds marginally inside QP
/// exhale queries.
///
/// A source provably without level-1 objects gets no level-1 map unless
/// `force_level1`: a wand side is reconstructed at each apply site from the
/// call's substituted types, and must have the shape the callee's identity
/// types gave it (an empty level-1 map is harmless, a missing one is a
/// `wand.not.found`).
pub(crate) fn im_boundary_maps<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    sources: &[(
        RustTyDecomposition<'vir>,
        vir::ExprRef<'vir>,
        vir::ExprSnap<'vir>,
    )],
    shared_sources: &[(
        RustTyDecomposition<'vir>,
        vir::ExprRef<'vir>,
        vir::ExprSnap<'vir>,
    )],
    force_level1: bool,
) -> Result<ImBoundaryMaps<'vir>, EncodeFullError<'vir, E>> {
    let tys = ImTys::new(deps);
    let unions = deps.require_dep::<MapUnionEnc>(())?;
    let param_im = deps.require_ref::<TyInteriorMutEnc>(RustTyDecomposition::param())?;
    let im0_snap = deps.require_dep::<Im0SnapEnc>(())?;
    // The leaves grouped by the type of their objects' holder (a reference
    // leaf by its referent type): leaves of one group may alias (two `&Cell`
    // arguments), so their maps are merged with the shared union; leaves of
    // different groups hold distinct objects, or objects deliberately shared
    // between holders of different types with amounts that SUM to the whole
    // (a `RefCell` and its `Ref` guards), and get a QP each. Each QP is
    // then over exactly the map a contract's read of that source requires.
    let mut groups: Vec<(
        RustTyDecomposition<'vir>,
        Option<vir::ExprMap<'vir>>,
        Option<vir::ExprMap<'vir>>,
        usize,
    )> = Vec::new();
    let mut lets0 = Vec::new();
    let mut lets1 = Vec::new();
    let mut src_lets = Vec::new();
    // Every map is `let`-bound under a descriptive name, so the emitted
    // contracts stay readable: each QP mentions its map by name instead of
    // repeating the map term in its trigger, guard and amount.
    let bind = |lets: &mut Vec<(vir::LocalDecl<'vir, vir::Map>, vir::ExprMap<'vir>)>,
                name: String,
                ty: vir::TypeMap<'vir>,
                value: vir::ExprMap<'vir>| {
        vir::with_vcx(|vcx| {
            let decl = vcx.mk_local_decl(vir::vir_format!(vcx, "{name}"), ty);
            lets.push((decl, value));
            vcx.mk_local_ex(decl)
        })
    };
    // `shared_sources` (by-value postcondition sources) contribute only the
    // shared component: their owned objects are consumed by the call, but
    // the objects behind references inside them belong to others and must
    // return to the caller.
    //
    // A by-value struct source is split into its leaf holders (see
    // `im_source_leaves`): a contract's read of a field (`result.count`)
    // then requires exactly the map its chunk was inhaled with, instead of
    // a sub-map of the struct's map, which the solver cannot extract inside
    // a permission check. The leaves of one value are disjoint; their maps
    // are merged like the type-level function merges its fields' maps.
    let mut leaf_idx = 0;
    for (shared_only, (ty, addr, snap)) in sources
        .iter()
        .map(|s| (false, s))
        .chain(shared_sources.iter().map(|s| (true, s)))
    {
        let mut leaves = Vec::new();
        im_source_leaves(deps, *ty, *addr, *snap, &mut leaves)?;
        for (ty, addr, snap) in leaves {
            let idx = leaf_idx;
            leaf_idx += 1;
            let group_key = match ty.ty.ref_data() {
                Some(ref_data) => ref_data.referent.decompose_normalize(ty.args),
                None => ty,
            };
            let group = match groups.iter().position(|g| g.0 == group_key) {
                Some(g) => g,
                None => {
                    groups.push((group_key, None, None, 0));
                    groups.len() - 1
                }
            };
            groups[group].3 += 1;
            let (r, s, t) = im0_source_triple(deps, ty, addr, snap)?;
            // The source's snapshot may be a heap read (`&mut` sources): bound
            // once per level, like the maps.
            let s = vir::with_vcx(|vcx| {
                let decl = vcx.mk_local_decl(vir::vir_format!(vcx, "im_source_{idx}"), s.ty());
                src_lets.push((decl, s));
                vcx.mk_local_ex(decl)
            });
            let ts = vir::with_vcx(|vcx| vcx.alloc_slice(&[t]));
            let (o, sh) = tys.split(param_im.l0.call()(r, s.upcast_ty(), ts, &[]));
            let u0 = if shared_only {
                sh
            } else {
                unions.disjoint.call()(o, sh)
            };
            let u0 = bind(&mut lets0, format!("im_perms0_{idx}"), tys.perm_map, u0);
            groups[group].1 = Some(match groups[group].1 {
                None => u0,
                Some(m) => unions.shared.call()(m, u0),
            });
            // Each source's level-1 amounts read level-0 state through the
            // source's OWN canonical map, `im0_snap(r, s, T)` — the same triple
            // that keys the pair. The map argument is then a function of the
            // triple, so two boundaries' amounts for the same source are equal
            // by plain congruence; a boundary-wide (joined) map would need the
            // nested-quantifier restrict-canonicity axiom to reconcile
            // differently-joined phrasings, which the solver cannot apply
            // spontaneously inside QP permission checks. Sound because a
            // permission closure takes only the object's `&self`: it can only
            // read state reachable from its own source. The heap-dependent
            // application must be `let`-bound OUTSIDE the QP (returned in
            // `map_lets` for the caller to wrap around the level-1 QP): embedded
            // directly in the map terms it defeats the instantiation of the
            // union functions' axioms.
            if !force_level1 && provably_no_level1_interior_mut(ty, &mut Default::default()) {
                continue;
            }
            let idn = if shared_only {
                im0_snap.shared
            } else {
                im0_snap.full
            };
            let src_map = bind(
                &mut lets1,
                format!("im_values0_{idx}"),
                tys.snap_map,
                idn.call()(r, s, t),
            );
            let (o, sh) = tys.split(param_im.l1.call()(r, s.upcast_ty(), src_map, ts, &[]));
            let u1 = if shared_only {
                sh
            } else {
                unions.disjoint.call()(o, sh)
            };
            let u1 = bind(&mut lets1, format!("im_perms1_{idx}"), tys.perm_map, u1);
            groups[group].2 = Some(match groups[group].2 {
                None => u1,
                Some(m) => unions.shared.call()(m, u1),
            });
        }
    }
    let mut m0 = Vec::new();
    let mut m1 = Vec::new();
    for (g, (_, g0, g1, leaves)) in groups.into_iter().enumerate() {
        if let Some(m) = g0 {
            m0.push(if leaves > 1 {
                bind(&mut lets0, format!("im_perms0_g{g}"), tys.perm_map, m)
            } else {
                m
            });
        }
        if let Some(m) = g1 {
            m1.push(if leaves > 1 {
                bind(&mut lets1, format!("im_perms1_g{g}"), tys.perm_map, m)
            } else {
                m
            });
        }
    }
    Ok(ImBoundaryMaps {
        m0,
        m1,
        lets0,
        lets1,
        src_lets,
    })
}

/// The leaf holders of a boundary source: a by-value struct that is not a
/// holder itself (no accessors of its own) is replaced by its fields, read
/// from its snapshot, recursively. Anything else (holders, enums, references,
/// generic values, boxes) is a leaf of its own.
fn im_source_leaves<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    ty: RustTyDecomposition<'vir>,
    addr: vir::ExprRef<'vir>,
    snap: vir::ExprSnap<'vir>,
    leaves: &mut Vec<(
        RustTyDecomposition<'vir>,
        vir::ExprRef<'vir>,
        vir::ExprSnap<'vir>,
    )>,
) -> Result<(), EncodeFullError<'vir, E>> {
    let fields = match ty.ty.get_structlike() {
        Some(data)
            if ty.ty.interior_mut.is_empty()
                && matches!(ty.ty.data.special, RustTySpecial::None) =>
        {
            &data.fields
        }
        _ => {
            leaves.push((ty, addr, snap));
            return Ok(());
        }
    };
    let ty_use = deps.require_dep::<TyUsePureEnc>(ty)?;
    let projs = ty_use.expect_variant_opt(None);
    for field in fields {
        let field_ty = field.ty().decompose_normalize(ty.args);
        let field_snap = projs[field.fid].read(snap.downcast_ty());
        im_source_leaves(deps, field_ty, addr, field_snap, leaves)?;
    }
    Ok(())
}

/// The level-0 and level-1 boundary permission maps (see
/// [`im_boundary_maps`]), one per group, referring to `let`-bound names
/// that `qp0`/`qp1` bind around the QPs.
pub(crate) struct ImBoundaryMaps<'vir> {
    m0: Vec<vir::ExprMap<'vir>>,
    m1: Vec<vir::ExprMap<'vir>>,
    lets0: Vec<(vir::LocalDecl<'vir, vir::Map>, vir::ExprMap<'vir>)>,
    lets1: Vec<(vir::LocalDecl<'vir, vir::Map>, vir::ExprMap<'vir>)>,
    src_lets: Vec<(vir::LocalDecl<'vir, vir::PSnap>, vir::ExprPSnap<'vir>)>,
}

impl<'vir> ImBoundaryMaps<'vir> {
    fn wrap(
        &self,
        lets: &[(vir::LocalDecl<'vir, vir::Map>, vir::ExprMap<'vir>)],
        mut expr: vir::ExprBool<'vir>,
    ) -> vir::ExprBool<'vir> {
        vir::with_vcx(|vcx| {
            for (decl, val) in lets.iter().rev() {
                expr = vcx.mk_let_expr(*decl, *val, expr);
            }
            for (decl, val) in self.src_lets.iter().rev() {
                expr = vcx.mk_let_expr(*decl, *val, expr);
            }
            expr
        })
    }

    fn qps<E: TaskEncoder>(
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
        maps: impl Iterator<Item = vir::ExprMap<'vir>>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let mut qps = Vec::new();
        for m in maps {
            qps.push(im_quant_perm(vcx, deps, m)?);
        }
        Ok(vcx.mk_conj(&qps))
    }

    /// The level-0 QPs (one per group, plus one over `extra` if given),
    /// under their `let`s.
    pub(crate) fn qp0<E: TaskEncoder>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
        extra: Option<vir::ExprMap<'vir>>,
    ) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
        let qps = Self::qps(vcx, deps, self.m0.iter().copied().chain(extra))?;
        Ok(self.wrap(&self.lets0, qps))
    }

    /// The level-1 QPs, under their `let`s; `None` if no source can have
    /// level-1 objects and there is no `extra` map.
    pub(crate) fn qp1<E: TaskEncoder>(
        &self,
        vcx: &'vir vir::VirCtxt<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
        extra: Option<vir::ExprMap<'vir>>,
    ) -> Result<Option<vir::ExprBool<'vir>>, EncodeFullError<'vir, E>> {
        if self.m1.is_empty() && extra.is_none() {
            return Ok(None);
        }
        let qps = Self::qps(vcx, deps, self.m1.iter().copied().chain(extra))?;
        Ok(Some(self.wrap(&self.lets1, qps)))
    }
}

/// The address argument of a source's `_IM_N` applications: `null`. The
/// maps do not depend on it (objects are keyed by identities from the
/// snapshot), and a fixed address keeps the map terms syntactically equal
/// across moves and call boundaries.
fn im_source_addr<'vir, Curr: 'vir, Next: 'vir>(
    _ty: RustTyDecomposition<'vir>,
    _addr: vir::ExprGenRef<'vir, Curr, Next>,
) -> vir::ExprGenRef<'vir, Curr, Next> {
    let null = vir::with_vcx(|vcx| vcx.mk_null());
    let ptr = null as *const _ as *const _;
    unsafe { &*ptr }
}

/// Lifts a generic-free type-value expression into any `Curr`/`Next` context
/// (the same device as `GArgsTy::get_ty`).
fn lift_ty_expr<'vir, Curr, Next>(e: vir::ExprTyVal<'vir>) -> vir::ExprGenTyVal<'vir, Curr, Next> {
    let ptr = e as *const _ as *const _;
    unsafe { &*ptr }
}

/// Casts a concrete-form snapshot into its `Param` (`s_Param`) form.
fn cast_snap_to_param<'vir, Curr: 'vir, Next: 'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    ty: RustTyDecomposition<'vir>,
    snap: vir::ExprGenSnap<'vir, Curr, Next>,
) -> Result<vir::ExprGenPSnap<'vir, Curr, Next>, EncodeFullError<'vir, E>> {
    // A param-typed value is already in `s_Param` form (and `CastersEnc`
    // rejects param-as-concrete tasks).
    if matches!(ty.ty.specifics, TySpecifics::Param(_)) {
        return Ok(snap.downcast_ty());
    }
    let caster = deps.require_dep::<GArgsCastEnc<Pure>>(Some(RustTyNormalized {
        param: RustTyDecomposition::param(),
        concrete: ty,
    }))?;
    Ok(caster.cast_to_callee_ctx(snap).downcast_ty())
}

/// The canonical level-0 map snapshot of the given sources: the `im0_join`
/// fold of their `im0_snap` applications (an empty snapshot map when there
/// are none). `shared_sources` are by-value postcondition sources; they use
/// the shared-only variant (their owned objects are consumed by the call,
/// so the full variant's permission precondition could not be evaluated).
pub(crate) fn im0_snap_sources<'vir, Curr: 'vir, Next: 'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    sources: &[(
        RustTyDecomposition<'vir>,
        vir::ExprGenRef<'vir, Curr, Next>,
        vir::ExprGenSnap<'vir, Curr, Next>,
    )],
    shared_sources: &[(
        RustTyDecomposition<'vir>,
        vir::ExprGenRef<'vir, Curr, Next>,
        vir::ExprGenSnap<'vir, Curr, Next>,
    )],
) -> Result<vir::ExprGenMap<'vir, Curr, Next>, EncodeFullError<'vir, E>> {
    let tys = ImTys::new(deps);
    let im0_snap = deps.require_dep::<Im0SnapEnc>(())?;
    let join = deps.require_dep::<Im0JoinEnc>(())?;
    let mut map = None;
    for (shared_only, (ty, addr, snap)) in sources
        .iter()
        .map(|s| (false, s))
        .chain(shared_sources.iter().map(|s| (true, s)))
    {
        let (r, s, t) = im0_source_triple(deps, *ty, *addr, *snap)?;
        let idn = if shared_only {
            im0_snap.shared
        } else {
            im0_snap.full
        };
        let app = idn.call()(r, s, lift_ty_expr(t));
        map = Some(match map {
            None => app,
            Some(m) => join.call()(m, app),
        });
    }
    Ok(map
        .unwrap_or_else(|| vir::with_vcx(|vcx| vcx.mk_map_empty_expr(tys.key.ty, vir::TYPE_PSNAP))))
}

/// The values of the level-0 objects in the shared component of the given
/// sources are as in the `old` state. Stated per object over the generic
/// snapshot function (not as an equality of two value maps): a later read of
/// such an object mentions its membership in the returned permission map,
/// which is what triggers this.
pub(crate) fn im_shared_frame<'vir, E: TaskEncoder>(
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    shared_sources: &[(
        RustTyDecomposition<'vir>,
        vir::ExprRef<'vir>,
        vir::ExprSnap<'vir>,
    )],
) -> Result<vir::ExprBool<'vir>, EncodeFullError<'vir, E>> {
    let tys = ImTys::new(deps);
    let param_im = deps.require_ref::<TyInteriorMutEnc>(RustTyDecomposition::param())?;
    let generic_snap = deps
        .require_dep::<TyImpureEnc>(RustTyDecomposition::param())?
        .data
        .ref_to_snap;
    let mut frames = Vec::with_capacity(shared_sources.len());
    for (ty, addr, snap) in shared_sources {
        let (r, s, t) = im0_source_triple(deps, *ty, *addr, *snap)?;
        frames.push(vir::with_vcx(|vcx| {
            let ts = vcx.alloc_slice(&[t]);
            let (_, shared) = tys.split(param_im.l0.call()(r, s.upcast_ty(), ts, &[]));
            let k = vcx.mk_local_decl("k", tys.key.ty);
            let k_ex = vcx.mk_local_ex(k);
            let obj = tys.key.destructors[0].call()(k_ex).downcast_ty::<vir::Ref>();
            let tyval = tys.key.destructors[1].call()(k_ex).downcast_ty::<vir::TyVal>();
            let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(shared));
            let amount = vcx
                .mk_map_lookup_expr(shared, k_ex)
                .downcast_ty::<vir::Perm>();
            let amount_pos = vcx
                .mk_unary_op_expr(
                    vir::UnOpKind::Not,
                    vcx.mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount),
                )
                .downcast_ty();
            let value = generic_snap.call()(obj, &[tyval], &[]);
            vcx.mk_forall_expr(
                vcx.alloc_slice(&[k]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::Implies,
                    vcx.mk_conj(&[in_dom, amount_pos]),
                    vcx.mk_eq_expr(value, vcx.mk_old_expr(value)),
                )
                .downcast_ty(),
            )
        }));
    }
    Ok(vir::with_vcx(|vcx| vcx.mk_conj(&frames)))
}

/// Whether `ty` provably has no reachable interior-mutable objects at all
/// (own accessors, fields, or referents, transitively). Unlike
/// [`provably_no_owned_interior_mut`], references recurse into their
/// referent: this gates *boundary* QPs, which cover behind-reference objects.
pub(crate) fn provably_no_interior_mut<'tcx>(
    tcx: ty::TyCtxt<'tcx>,
    ty: ty::Ty<'tcx>,
    seen: &mut rustc_hash::FxHashSet<ty::Ty<'tcx>>,
) -> bool {
    if !seen.insert(ty) {
        return true;
    }
    match *ty.kind() {
        ty::TyKind::Adt(adt, args) => {
            adt.is_unsafe_cell()
                || (crate::encoders::get_type_interior_mut(ty).is_empty()
                    && adt
                        .variants()
                        .iter()
                        .flat_map(|variant| variant.fields.iter())
                        .all(|field| provably_no_interior_mut(tcx, field.ty(tcx, args), seen)))
        }
        ty::TyKind::Tuple(tys) => tys.iter().all(|t| provably_no_interior_mut(tcx, t, seen)),
        ty::TyKind::Array(elem, _) | ty::TyKind::Slice(elem) => {
            provably_no_interior_mut(tcx, elem, seen)
        }
        ty::TyKind::Ref(_, inner, _) => provably_no_interior_mut(tcx, inner, seen),
        // A raw pointer grants no permission to its pointee, so it
        // contributes no interior-mutable objects (see the encoder).
        ty::TyKind::RawPtr(..) => true,
        ty::TyKind::Bool
        | ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_)
        | ty::TyKind::Float(_)
        | ty::TyKind::Str
        | ty::TyKind::Never
        | ty::TyKind::FnDef(..)
        | ty::TyKind::FnPtr(..) => true,
        _ => false,
    }
}

/// Whether `ty` provably has no reachable LEVEL-1 interior-mutable objects:
/// the walk of the `s_Ty_IM_1` encoding, with generic and opaque types
/// unknown. For such a type the level-1 maps are empty, so its level-1 QP
/// (and the heap-dependent level-0 value map it reads) can be omitted. This
/// matters beyond size: Silicon relates every pair of heap-dependent
/// function applications with quantified preconditions, so verification
/// time is quadratic in the number of value-map reads.
pub(crate) fn provably_no_level1_interior_mut<'tcx>(
    ty: RustTyDecomposition<'tcx>,
    seen: &mut rustc_hash::FxHashSet<RustTyDecomposition<'tcx>>,
) -> bool {
    if !seen.insert(ty) {
        return true;
    }
    if ty.ty.interior_mut.iter().any(|im| accessor_level(*im) == 1) {
        return false;
    }
    if matches!(ty.ty.data.special, RustTySpecial::UnsafeCell) {
        return true;
    }
    let mut all = |fields: &mut dyn Iterator<Item = LazyRustTy<'tcx>>| {
        let mut no_level1 = true;
        for f in fields {
            no_level1 &= provably_no_level1_interior_mut(f.decompose_normalize(ty.args), seen);
        }
        no_level1
    };
    match &ty.ty.specifics {
        TySpecifics::Primitive(_)
        | TySpecifics::Raw(_)
        | TySpecifics::Builtin(_)
        | TySpecifics::ArrayLike(_) => true,
        TySpecifics::Param(_) | TySpecifics::Opaque(_) => false,
        TySpecifics::ImmRef(data) => all(&mut std::iter::once(data.referent)),
        TySpecifics::MutRef(data) => all(&mut std::iter::once(data.referent)),
        TySpecifics::StructLike(data) => all(&mut data.fields.iter().map(|f| f.ty())),
        TySpecifics::EnumLike(data) => all(&mut data
            .variants
            .iter()
            .flat_map(|v| v.inner.fields.iter().map(|f| f.ty()))),
    }
}

/// The full interior-mutability boundary QPs over the merged maps of the
/// given `(type, rust type, address, snapshot)` sources, as used at loop
/// boundaries: the level-0 QP, then the level-1 QP under a `let`-bound
/// level-0 map snapshot (mirroring `mk_qps` in the method encoder, including
/// the `let`-bound snapshots). Returns `None` if no source can have any
/// interior-mutable objects.
pub(crate) fn boundary_im_qps<'vir, E: TaskEncoder>(
    vcx: &'vir vir::VirCtxt<'vir>,
    deps: &mut task_encoder::TaskEncoderDependencies<'vir, E>,
    sources: &[(
        RustTyDecomposition<'vir>,
        ty::Ty<'vir>,
        vir::ExprRef<'vir>,
        vir::ExprSnap<'vir>,
    )],
) -> Result<Option<vir::ExprBool<'vir>>, EncodeFullError<'vir, E>> {
    let relevant = sources
        .iter()
        .filter(|(_, rust_ty, _, _)| {
            !provably_no_interior_mut(vcx.tcx(), *rust_ty, &mut Default::default())
        })
        .collect::<Vec<_>>();
    if relevant.is_empty() {
        return Ok(None);
    }
    let mut lets = Vec::with_capacity(relevant.len());
    let mut im0_sources = Vec::with_capacity(relevant.len());
    for (idx, (ty, _, addr, snap)) in relevant.iter().enumerate() {
        let decl = vcx.mk_local_decl(vir::vir_format!(vcx, "im_snap_{idx}"), snap.ty());
        lets.push((decl, *snap));
        im0_sources.push((*ty, *addr, vcx.mk_local_ex(decl)));
    }
    let maps = im_boundary_maps(deps, &im0_sources, &[], false)?;
    let mut qps = vec![maps.qp0(vcx, deps, None)?];
    if let Some(qp1) = maps.qp1(vcx, deps, None)? {
        qps.push(qp1);
    }
    // Self-framing order (see `mk_qps` in the method encoder).
    let mut expr = vcx.mk_conj(&qps);
    for (decl, val) in lets.into_iter().rev() {
        expr = vcx.mk_let_expr(decl, val, expr);
    }
    Ok(Some(expr))
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
    (
        vir::Ref,
        vir::Snap,
        vir::Map,
        vir::ManyTyVal,
        vir::ManyCSnap,
    ),
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
                                extra_functions: &mut Vec<vir::Function<'vir>>,
                                level: usize|
             -> Result<_, EncodeFullError<'vir, Self>> {
                let snap_map = (level == 1).then_some(im0_map_ex);
                let mut field_enc = TyInteriorMutField {
                    vcx,
                    tys: tys.clone(),
                    unions,
                    deps,
                    params: task_key.params,
                    generics: params.clone(),
                    extra_functions,
                    param_exprs: params.ty_exprs(),
                    const_exprs: params.const_exprs(),
                    snap: snap_ex,
                    level,
                    snap_map,
                };
                // The recursive (field/ref) contributions.
                let body: Option<ImPair> =
                    match &task_key.zip(vcx.alloc(pure.zip(impure))).specifics {
                        _ if matches!(task_key.data.special, RustTySpecial::UnsafeCell) => {
                            Some(field_enc.empty_pair())
                        }
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
                        // TODO: fold the elements' pairs (the element type and
                        // length are generic here, so this needs a recursive or
                        // per-instantiation formulation). The empty pair is a
                        // sound under-approximation of the granted permissions:
                        // plain arrays have no interior-mutable objects, and an
                        // array of e.g. `Cell`s fails to verify at use (its
                        // objects never receive permission) instead of crashing.
                        TySpecifics::ArrayLike(_) => Some(field_enc.empty_pair()),
                        TySpecifics::StructLike(data) => Some(field_enc.all_in_struct(data)?),
                        TySpecifics::EnumLike(enum_data) => Some(field_enc.all_in_enum(enum_data)?),
                    };
                // This type's own accessors of this level (e.g. the `*mut T`
                // of a `Cell` at level 0, of a `RefCell` at level 1). An
                // inline accessor's object lives in the value itself, so it
                // belongs to the owned map; a stored-pointer accessor's
                // object (e.g. what a `Ref` guard points to) lives behind
                // the pointer, so it belongs to the shared map: it is not
                // moved with the holder, and it outlives it.
                let mut own: vir::ExprMap<'vir> = field_enc.tys.empty_map();
                let mut has_own = false;
                let mut behind: vir::ExprMap<'vir> = field_enc.tys.empty_map();
                let mut has_behind = false;
                for im in task_key.interior_mut.iter() {
                    if accessor_level(*im) != level {
                        continue;
                    }
                    let (key, perm, stored_pointer) =
                        field_enc.own_object(*im, task_key, addr_ex)?;
                    if stored_pointer {
                        behind = vcx.mk_map_update_expr(behind, key, perm);
                        has_behind = true;
                    } else {
                        own = vcx.mk_map_update_expr(own, key, perm);
                        has_own = true;
                    }
                }
                assert!(body.is_some() || !(has_own || has_behind));
                let combined = body.map(|b| ImPair {
                    owned: if has_own {
                        field_enc.unions.disjoint.call()(b.owned, own)
                    } else {
                        b.owned
                    },
                    shared: if has_behind {
                        field_enc.unions.shared.call()(b.shared, behind)
                    } else {
                        b.shared
                    },
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

            let mut extra_fns = Vec::new();
            let l0_posts = encode_level(deps, &mut extra_fns, 0)?;
            let l0_fn = vcx.mk_function(
                l0_idn,
                (addr, snap, params.ty_decls(), params.const_decls()),
                &[],
                vcx.alloc_slice(&l0_posts),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            let l1_posts = encode_level(deps, &mut extra_fns, 1)?;
            let l1_fn = vcx.mk_function(
                l1_idn,
                (addr, snap, im0_map, params.ty_decls(), params.const_decls()),
                &[],
                vcx.alloc_slice(&l1_posts),
                Some(&vir::DecreasesGenData::Star),
                None,
            );
            let mut functions = vec![l0_fn, l1_fn];
            functions.append(&mut extra_fns);
            Ok((functions, ()))
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

pub(crate) type ImIdFn<'vir> =
    vir::FunctionIdn<'vir, (vir::Snap, vir::ManyTyVal, vir::ManyCSnap), vir::Ref>;

/// The `im_id_*` function of the (inline) `#[interior_mut]` accessor `im`:
/// the identity keying its object, as a function of the containing value's
/// snapshot (and the containing type's generics). The snapshot of a holder
/// is stable: its mutable contents live in the interior-mutability heap and
/// only their `UnsafeCell` identities are in the snapshot. Emitted by
/// `TyInteriorMutEnc` for the accessor's type.
pub(crate) fn im_id_function<'vir>(
    vcx: &'vir vir::VirCtxt<'vir>,
    im: DefId,
    holder_snap: vir::TypeSnap<'vir>,
    generics: &GenericParams<'vir>,
) -> ImIdFn<'vir> {
    vir::FunctionIdn::new(
        vir::vir_format_identifier!(vcx, "im_id_{}", vcx.tcx().def_path_str(im)),
        (holder_snap, generics.ty_args(), generics.const_args()),
        vir::TYPE_REF,
    )
}

struct TyInteriorMutField<'a, 'vir> {
    vcx: &'vir vir::VirCtxt<'vir>,
    tys: ImTys<'vir>,
    unions: MapUnionFns<'vir>,
    deps: &'a mut task_encoder::TaskEncoderDependencies<'vir, TyInteriorMutEnc>,
    params: GParams<'vir>,
    generics: GenericParams<'vir>,
    /// Additional emitted functions (the per-accessor `im_id_*` identity
    /// functions), collected into the encoder's output.
    extra_functions: &'a mut Vec<vir::Function<'vir>>,
    param_exprs: &'a [vir::ExprTyVal<'vir>],
    const_exprs: &'a [vir::ExprCSnap<'vir>],
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
    ) -> Result<
        (vir::Expr<'vir, vir::Pair>, vir::ExprPerm<'vir>, bool),
        EncodeFullError<'vir, TyInteriorMutEnc>,
    > {
        let vcx = self.vcx;
        let signature = vcx.tcx().fn_sig(im).skip_binder();
        let rust_input_ty = signature.inputs().skip_binder()[0];
        let input_ty = RustTyDecomposition::from_ty(rust_input_ty, task_key.data.params);
        let output = signature.output().skip_binder();
        let inner = match *output.kind() {
            ty::TyKind::RawPtr(inner, _) => inner,
            _ => panic!(
                "expected raw pointer output for interior mutability, got {:?}",
                output
            ),
        };
        let stored_pointer = crate::encoders::get_field_projection(im);
        let ref_ = if let Some(path) = &stored_pointer {
            // A `#[field_projection]` accessor returns a pointer STORED in
            // the value (e.g. a guard's pointer to the guarded object): the
            // object's address is the pointer's address, read from the
            // snapshot. It is stable under moves of the holder, and the
            // object lives behind the pointer rather than in the holder.
            let self_ty = rust_input_ty.builtin_deref(true).unwrap();
            let (ptr_ty, ptr_snap, _) = crate::encoders::ty::use_pure::project_field_path(
                vcx,
                self.deps,
                task_key.data.params,
                path,
                self_ty,
                self.snap,
                addr_ex,
            )?
            .unwrap_or_else(|message| panic!("invalid `#[field_projection]`: {message}"));
            let ptr_use = self
                .deps
                .require_dep::<TyUsePureEnc>(RustTyDecomposition::from_ty(
                    ptr_ty,
                    task_key.data.params,
                ))?;
            ptr_use.expect_raw().address_access(ptr_snap.downcast_ty())
        } else {
            // The object's identity: a per-accessor abstract function of the
            // containing value's snapshot, which is stable under moves (it is
            // copied) and under mutation of the contents (those live in the
            // interior-mutability heap; the snapshot holds only identities).
            // The accessor's own pure function is tied to it by a
            // postcondition (see `FunctionEnc`), so pointer equalities in
            // specs imply key equalities.
            let im_id = im_id_function(vcx, im, self.snap.ty(), &self.generics);
            let s = vcx.mk_local_decl("snap", self.snap.ty());
            self.extra_functions.push(vcx.mk_function(
                im_id,
                (s, self.generics.ty_decls(), self.generics.const_decls()),
                &[],
                &[],
                Some(&vir::DecreasesGenData::Star),
                None,
            ));
            im_id.call()(self.snap, self.param_exprs, self.const_exprs)
        };
        let ty_ = RustTyDecomposition::from_ty(inner, task_key.data.params);
        let ty_expr = ty_identity_expr(self.deps, ty_);
        let key = (self.tys.key.constructor)(&[ref_.as_dyn(), ty_expr.as_dyn()]);
        let perm = match crate::encoders::get_interior_mut_perm(im) {
            Some(perm_def_id) => {
                self.eval_perm(perm_def_id, input_ty, addr_ex, task_key.data.params)?
            }
            None => write_perm(vcx),
        };
        Ok((key, perm, stored_pointer.is_some()))
    }

    /// Evaluates the `#[interior_mut(EXPR)]` permission expression (the spec
    /// closure `perm_def_id`) into a Viper `Perm` amount. The closure's
    /// `&self` argument is built from the holder's snapshot (with the
    /// object's address and arbitrary metadata): the permission amount is a
    /// function of the holder's identities and the IM-QP state (the closure
    /// reads any interior-mutable state it needs through the map, e.g. via
    /// `refcell_count`).
    fn eval_perm(
        &mut self,
        perm_def_id: DefId,
        input_ty: RustTyDecomposition<'vir>,
        addr_ex: vir::ExprRef<'vir>,
        params: GParams<'vir>,
    ) -> Result<vir::ExprPerm<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let ref_data = input_ty.ty.ref_data().unwrap();
        let metadata_ty = ref_data.metadata.decompose_normalize(input_ty.args);
        let metadata = match self
            .deps
            .require_dep::<TyUsePureEnc>(metadata_ty)
            .unwrap()
            .zst_to_snap()
        {
            Some(m) => m.upcast_ty(),
            None => self
                .deps
                .require_ref::<TyUsePureEnc>(metadata_ty)
                .unwrap()
                .arbitrary_to_snap(),
        };
        // The `&self` argument refers to the holder's actual snapshot: the
        // permission expression reads the holder's interior-mutable state
        // (e.g. a `RefCell`'s borrow count) through keys derived from it.
        let input = self
            .deps
            .require_dep::<TyUsePureEnc>(input_ty)
            .unwrap()
            .expect_immref()
            .prim_to_snap(addr_ex, metadata, self.snap);
        let call = CallTaskDescription::new(params, params.rust_params(), perm_def_id);
        let perm_func = self.deps.require_dep::<FunctionCallEnc>(call).unwrap();
        let args = vec![input.upcast_ty()];
        // A level-1 permission closure is `#[pure_unstable(true)]`: it takes
        // the level-0 map (this level-1 function's `im_0_map` parameter) to
        // read level-0 interior-mutable state (e.g. a `RefCell`'s borrow
        // count). A level-0 permission closure is plain pure.
        let perm_snap = if perm_func.is_pure_unstable() {
            // Pass the minimal map: the level-0 map restricted to the keys
            // reachable from the closure's `&self` argument, so applications
            // built from differently-phrased boundary maps compare equal
            // (see `MapRestrictEnc`).
            let input_im = self.deps.require_dep::<TyInteriorMutUseEnc>(input_ty)?;
            let restrict = self.deps.require_dep::<MapRestrictEnc>(())?.restrict;
            let m0 = merge_pairs(
                &self.tys,
                &self.unions,
                [input_im.get_0(addr_ex, input.upcast_ty())],
            );
            let map = vir::with_vcx(|vcx| {
                restrict.call()(self.snap_map.unwrap(), vcx.mk_map_domain_expr(m0))
            });
            perm_func.call_pure_unstable(args, map)
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
        let (inner, _) = *data;
        let ty = inner.referent.decompose(self.params);
        let addr = self.vcx.mk_null();
        // The referent value embedded in a mutable reference's snapshot is
        // arbitrary (freshly havocked at each assignment), so maps built from
        // it do not compare equal across program points. The canonical
        // arbitrary snapshot is used instead: the maps then depend only on
        // the referent address, which is what keys the referent's
        // interior-mutable objects. (Objects whose keys sit in the referent
        // *value*, e.g. behind a further reference field, are not reachable
        // through a mutable reference this way; that is a known
        // incompleteness, consistent on both sides of every exhale/inhale.)
        let snap = self
            .deps
            .require_ref::<TyUsePureEnc>(ty)?
            .arbitrary_to_snap();
        self.referent_pair(ty, addr, snap)
    }

    /// A shared reference collapses the referent's whole pair into the shared
    /// side: everything below it is only reachable behind a `&`.
    fn all_in_immref(
        &mut self,
        data: &<(RustTyDatas, (PureTyDatas, ImpureTyDatas)) as TyDatas<'vir>>::ImmRefData,
    ) -> Result<ImPair<'vir>, EncodeFullError<'vir, TyInteriorMutEnc>> {
        let (inner, (pure, _)) = *data;
        let ty = inner.referent.decompose(self.params);
        let addr = self.vcx.mk_null();
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
        for (field, (pure, _)) in data.fields.iter() {
            let ty = field.decompose(self.params);
            // Objects are keyed by identities in the snapshot, not by
            // addresses: every `_IM_N` application takes `null`, so that the
            // maps of a value are the same terms wherever it is reached.
            let addr = self.vcx.mk_null();
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

/// The canonical level-0 interior-mutability value snapshot
/// `im0_snap(r, s, T): Map[Pair2[Ref, Type], s_Param]`: the current values
/// of the level-0 interior-mutable objects of the `T`-typed value at `r`
/// with (`Param`-form) snapshot `s`. One shared heap-dependent function, so
/// that every boundary (pre/post QPs, loop invariants, moves, spec-site
/// materializations) produces literally the same application for the same
/// source: the level-1 `_IM_1` functions are opaque in their map argument,
/// and plain congruence (same function, equal arguments, unchanged
/// footprint) then replaces any canonicity reasoning about
/// differently-phrased map terms. The precondition is a `wildcard` QP
/// (reading needs any positive amount), so aliasing sources and
/// partially-consumed exhale states pose no accounting problems.
pub(crate) struct Im0SnapEnc;

pub(crate) type Im0SnapFn<'vir> =
    vir::FunctionIdn<'vir, (vir::Ref, vir::PSnap, vir::TyVal), vir::Map>;
pub(crate) type Im1SnapFn<'vir> =
    vir::FunctionIdn<'vir, (vir::Ref, vir::PSnap, vir::Map, vir::TyVal), vir::Map>;

#[derive(Debug, Clone, Copy)]
pub(crate) struct Im0SnapFns<'vir> {
    /// `im0_snap`: over the full (owned + shared) level-0 union.
    pub(crate) full: Im0SnapFn<'vir>,
    /// `im0_snap_shared`: over the shared component only. Used for by-value
    /// arguments in postconditions: their owned objects are consumed by the
    /// call, so the full variant's precondition could not be evaluated there.
    pub(crate) shared: Im0SnapFn<'vir>,
    /// `im1_snap(r, s, im0, T)`: the level-1 objects, for `#[pure_unstable]`
    /// functions that read level-1 state. The level-0 value map `im0` is a
    /// parameter (the caller binds `im0_snap(r, s, T)` once): two separate
    /// evaluations of a heap-dependent function are not syntactically equal.
    pub(crate) level1: Im1SnapFn<'vir>,
}

impl TaskEncoder for Im0SnapEnc {
    task_encoder::encoder_cache!(Im0SnapEnc);
    const ENCODER_NAME: &'static str = "interior mutability level-0 snapshot encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = Im0SnapFns<'vir>;
    type OutputFullLocal<'vir> = Vec<vir::Function<'vir>>;
    type EncodingError = TyInteriorMutError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let tys = ImTys::new(deps);
        let unions = deps.require_dep::<MapUnionEnc>(())?;
        let param_im = deps.require_ref::<TyInteriorMutEnc>(RustTyDecomposition::param())?;
        let param_ref = deps.require_dep::<TyImpureEnc>(RustTyDecomposition::param())?;
        let generic_pred = param_ref.data.ref_to_pred;
        let generic_snap = param_ref.data.ref_to_snap;
        let default = deps.require_dep::<MapRestrictEnc>(())?.default;

        vir::with_vcx(|vcx| {
            let mut funcs = Vec::new();
            let mut build = |name: &'static str, shared_only: bool| {
                let idn: Im0SnapFn<'vir> = vir::FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "{name}"),
                    (vir::TYPE_REF, vir::TYPE_PSNAP, vir::TYPE_TYVAL),
                    tys.snap_map,
                );

                let r = vcx.mk_local_decl("r", vir::TYPE_REF);
                let s = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
                let t = vcx.mk_local_decl("T", vir::TYPE_TYVAL);
                let r_ex = vcx.mk_local_ex(r);
                let s_ex: vir::ExprPSnap<'vir> = vcx.mk_local_ex(s);
                let t_ex = vcx.mk_local_ex(t);
                let pair =
                    param_im.l0.call()(r_ex, s_ex.upcast_ty(), vcx.alloc_slice(&[t_ex]), &[]);
                let (owned, shared) = tys.split(pair);
                let u = if shared_only {
                    shared
                } else {
                    unions.disjoint.call()(owned, shared)
                };

                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                let addr = tys.key.destructors[0].call()(k_ex).downcast_ty::<vir::Ref>();
                let tyval = tys.key.destructors[1].call()(k_ex).downcast_ty::<vir::TyVal>();
                let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(u));
                let amount = vcx.mk_map_lookup_expr(u, k_ex).downcast_ty::<vir::Perm>();
                let amount_pos = vcx
                    .mk_unary_op_expr(
                        vir::UnOpKind::Not,
                        vcx.mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount),
                    )
                    .downcast_ty();
                let wildcard = vcx.mk_wildcard();

                // requires: forall k :: { k in domain(u) }
                //   k in domain(u) && !(none >= u[k]) ==>
                //   acc(p_Param(k._2_0, k._2_1), wildcard)
                // where u = im_map_union_disjoint(IM_0(r, s, T)._2_0, ..._2_1)
                // (or just ..._2_1 for the shared variant).
                let pred =
                    vcx.mk_predicate_app_expr(generic_pred(addr, &[tyval], &[])(Some(wildcard)));
                let pre = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[k]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        vcx.mk_conj(&[in_dom, amount_pos]),
                        pred,
                    )
                    .downcast_ty(),
                );

                // ensures: domain(result) == domain(u)
                let result_map: vir::ExprMap<'vir> = vcx.mk_result(tys.snap_map);
                let dom_post = vcx.mk_eq_expr(
                    vcx.mk_map_domain_expr(result_map),
                    vcx.mk_map_domain_expr(u),
                );
                let in_result = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(result_map));
                let lookup: vir::ExprPSnap<'vir> =
                    vcx.mk_map_lookup_expr(result_map, k_ex).downcast_ty();
                // ensures: forall k :: { k in domain(u) } { k in domain(result) }
                //   k in domain(u) && !(none >= u[k]) ==>
                //   result[k] == p_Param_snap(k._2_0, k._2_1)
                let snap_at = generic_snap.call()(addr, &[tyval], &[]).downcast_ty::<vir::PSnap>();
                let entry_post = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[k]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom]), vcx.mk_trigger(&[in_result])]),
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        vcx.mk_conj(&[in_dom, amount_pos]),
                        vcx.mk_eq_expr(lookup, snap_at),
                    )
                    .downcast_ty(),
                );
                // ensures: forall k :: { k in domain(u) } { k in domain(result) }
                //   k in domain(u) && none >= u[k] ==> result[k] == im_snap_default(k)
                // (level-0 amounts are positive in practice; the default keeps
                // the result fully determined either way).
                let no_amount = vcx
                    .mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount)
                    .downcast_ty();
                let default_post = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[k]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom]), vcx.mk_trigger(&[in_result])]),
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        vcx.mk_conj(&[in_dom, no_amount]),
                        vcx.mk_eq_expr(lookup, default.call()(k_ex)),
                    )
                    .downcast_ty(),
                );

                funcs.push(vcx.mk_function(
                    idn,
                    (r, s, t),
                    vcx.alloc_slice(&[pre]),
                    vcx.alloc_slice(&[dom_post, entry_post, default_post]),
                    None,
                    None,
                ));
                idn
            };
            let full = build("im0_snap", false);
            let shared = build("im0_snap_shared", true);

            // `im1_snap(r, s, im0, T)`: the values of the level-1 objects,
            // for `#[pure_unstable]` functions that read level-1 state (e.g.
            // a `RefCell`'s value). The level-1 permission maps read level-0
            // state through the `im0` parameter.
            let level1 = {
                let idn: Im1SnapFn<'vir> = vir::FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "im1_snap"),
                    (
                        vir::TYPE_REF,
                        vir::TYPE_PSNAP,
                        tys.snap_map,
                        vir::TYPE_TYVAL,
                    ),
                    tys.snap_map,
                );
                let r = vcx.mk_local_decl("r", vir::TYPE_REF);
                let s = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
                let m0 = vcx.mk_local_decl("im0", tys.snap_map);
                let t = vcx.mk_local_decl("T", vir::TYPE_TYVAL);
                let r_ex = vcx.mk_local_ex(r);
                let s_ex: vir::ExprPSnap<'vir> = vcx.mk_local_ex(s);
                let t_ex = vcx.mk_local_ex(t);
                let ts = vcx.alloc_slice(&[t_ex]);
                let (o1, sh1) = tys.split(param_im.l1.call()(
                    r_ex,
                    s_ex.upcast_ty(),
                    vcx.mk_local_ex(m0),
                    ts,
                    &[],
                ));
                let u1 = unions.disjoint.call()(o1, sh1);

                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                let addr = tys.key.destructors[0].call()(k_ex).downcast_ty::<vir::Ref>();
                let tyval = tys.key.destructors[1].call()(k_ex).downcast_ty::<vir::TyVal>();
                let result_map: vir::ExprMap<'vir> = vcx.mk_result(tys.snap_map);
                let lookup: vir::ExprPSnap<'vir> =
                    vcx.mk_map_lookup_expr(result_map, k_ex).downcast_ty();
                let snap_at = generic_snap.call()(addr, &[tyval], &[]).downcast_ty::<vir::PSnap>();
                // Per level map `u`: the wildcard precondition QP and the
                // entry postcondition for positive amounts.
                let level = |u: vir::ExprMap<'vir>| {
                    let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(u));
                    let amount = vcx.mk_map_lookup_expr(u, k_ex).downcast_ty::<vir::Perm>();
                    let amount_pos = vcx
                        .mk_unary_op_expr(
                            vir::UnOpKind::Not,
                            vcx.mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount),
                        )
                        .downcast_ty();
                    let guard = vcx.mk_conj(&[in_dom, amount_pos]);
                    let pred = vcx.mk_predicate_app_expr(generic_pred(addr, &[tyval], &[])(Some(
                        vcx.mk_wildcard(),
                    )));
                    let pre = vcx.mk_forall_expr(
                        vcx.alloc_slice(&[k]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                        vcx.mk_bin_op_expr(vir::BinOpKind::Implies, guard, pred)
                            .downcast_ty(),
                    );
                    let entry = vcx.mk_forall_expr(
                        vcx.alloc_slice(&[k]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::Implies,
                            guard,
                            vcx.mk_conj(&[
                                vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(result_map)),
                                vcx.mk_eq_expr(lookup, snap_at),
                            ]),
                        )
                        .downcast_ty(),
                    );
                    (pre, entry)
                };
                let (pre, post) = level(u1);
                funcs.push(vcx.mk_function(
                    idn,
                    (r, s, m0, t),
                    vcx.alloc_slice(&[pre]),
                    vcx.alloc_slice(&[post]),
                    None,
                    None,
                ));
                idn
            };
            deps.emit_output_ref((), ())?;
            Ok((
                funcs,
                Im0SnapFns {
                    full,
                    shared,
                    level1,
                },
            ))
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

/// Join of level-0 value-snapshot maps, for boundaries with several sources.
/// Left-biased on overlaps; both sides read the same state, so overlapping
/// (aliased) entries agree anyway.
pub(crate) struct Im0JoinEnc;

pub(crate) type Im0JoinFn<'vir> = vir::FunctionIdn<'vir, (vir::Map, vir::Map), vir::Map>;

impl TaskEncoder for Im0JoinEnc {
    task_encoder::encoder_cache!(Im0JoinEnc);
    const ENCODER_NAME: &'static str = "interior mutability snapshot join encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = Im0JoinFn<'vir>;
    type OutputFullLocal<'vir> = vir::Function<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let tys = ImTys::new(deps);
        vir::with_vcx(|vcx| {
            let idn: Im0JoinFn<'vir> = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "im0_join"),
                (tys.snap_map, tys.snap_map),
                tys.snap_map,
            );
            deps.emit_output_ref((), ())?;

            let a = vcx.mk_local_decl("a", tys.snap_map);
            let b = vcx.mk_local_decl("b", tys.snap_map);
            let a_ex = vcx.mk_local_ex(a);
            let b_ex = vcx.mk_local_ex(b);
            let result: vir::ExprMap<'vir> = vcx.mk_result(tys.snap_map);
            let dom = |m| vcx.mk_map_domain_expr(m);
            // domain(result) == domain(a) union domain(b)
            let dom_post = vcx.mk_eq_expr(
                dom(result),
                vcx.mk_anyset_op_expr(vir::CollectionBinOpKind::Union, dom(a_ex), dom(b_ex))
                    .downcast_ty::<vir::Set>(),
            );
            // forall k :: { k in domain(a) } k in domain(a) ==> result[k] == a[k]
            let left_post = {
                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                let in_a = vcx.mk_set_in_expr(k_ex, dom(a_ex));
                let eq = vcx.mk_eq_expr(
                    vcx.mk_map_lookup_expr(result, k_ex)
                        .downcast_ty::<vir::PSnap>(),
                    vcx.mk_map_lookup_expr(a_ex, k_ex)
                        .downcast_ty::<vir::PSnap>(),
                );
                vcx.mk_forall_expr(
                    vcx.alloc_slice(&[k]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_a])]),
                    vcx.mk_bin_op_expr(vir::BinOpKind::Implies, in_a, eq)
                        .downcast_ty(),
                )
            };
            // forall k :: { k in domain(b) }
            //   k in domain(b) && !(k in domain(a)) ==> result[k] == b[k]
            let right_post = {
                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                let in_a = vcx.mk_set_in_expr(k_ex, dom(a_ex));
                let in_b = vcx.mk_set_in_expr(k_ex, dom(b_ex));
                let not_in_a = vcx
                    .mk_unary_op_expr(vir::UnOpKind::Not, in_a.upcast_ty())
                    .downcast_ty();
                let eq = vcx.mk_eq_expr(
                    vcx.mk_map_lookup_expr(result, k_ex)
                        .downcast_ty::<vir::PSnap>(),
                    vcx.mk_map_lookup_expr(b_ex, k_ex)
                        .downcast_ty::<vir::PSnap>(),
                );
                vcx.mk_forall_expr(
                    vcx.alloc_slice(&[k]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_b])]),
                    vcx.mk_bin_op_expr(vir::BinOpKind::Implies, vcx.mk_conj(&[in_b, not_in_a]), eq)
                        .downcast_ty(),
                )
            };
            let func = vcx.mk_function(
                idn,
                (a, b),
                &[],
                vcx.alloc_slice(&[dom_post, left_post, right_post]),
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
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let tys = ImTys::new(deps);
        vir::with_vcx(|vcx| {
            // The unions are total, heap-independent functions, so they are
            // encoded as domain functions with FLAT (single-level) axioms:
            // as postconditions on a Viper `function` these facts sit inside
            // a nested quantifier (the function's definitional axiom around
            // the pointwise forall), and the inner level reliably fails to
            // instantiate inside Silicon's QP permission checks (e.g. the
            // `im0_snap` wildcard precondition against a boundary QP over a
            // union result). Flat axioms with the application term in the
            // trigger make those checks one direct instantiation.
            let mut funcs = Vec::new();
            let mut axioms = Vec::new();
            let mut build = |name: &'static str, disjoint: bool| {
                let idn: MapUnionFn<'vir> = vir::FunctionIdn::new(
                    vir::vir_format_identifier!(vcx, "{name}"),
                    (tys.perm_map, tys.perm_map),
                    tys.perm_map,
                );
                funcs.push(vcx.mk_domain_function(idn, false, None));
                let a = vcx.mk_local_decl("a", tys.perm_map);
                let b = vcx.mk_local_decl("b", tys.perm_map);
                let a_ex = vcx.mk_local_ex(a);
                let b_ex = vcx.mk_local_ex(b);
                let app = idn.call()(a_ex, b_ex);
                let dom = |m| vcx.mk_map_domain_expr(m);
                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                // forall a, b :: { f(a, b) }
                //   domain(f(a, b)) == domain(a) union domain(b)
                let dom_ax = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[a, b]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[app])]),
                    vcx.mk_eq_expr(
                        dom(app),
                        vcx.mk_anyset_op_expr(
                            vir::CollectionBinOpKind::Union,
                            dom(a_ex),
                            dom(b_ex),
                        )
                        .downcast_ty::<vir::Set>(),
                    ),
                );
                axioms.push(
                    vcx.mk_domain_axiom(vir::vir_format_identifier!(vcx, "ax_{name}_dom"), dom_ax),
                );
                // forall a, b, k :: { f(a, b), k in domain(m) }
                //   k in domain(m) ==> k in domain(f(a, b)) && f(a, b)[k] == m[k]
                // (for m in {a, b}; the result-domain membership is stated
                // directly so the fact is one instantiation away from a
                // permission check that contains the `k in domain(m)` term).
                let mut lookup_ax = |m: vir::ExprMap<'vir>, side: &str| {
                    let in_dom = vcx.mk_set_in_expr(k_ex, dom(m));
                    let in_result = vcx.mk_set_in_expr(k_ex, dom(app));
                    let eq = vcx.mk_eq_expr(
                        vcx.mk_map_lookup_expr(app, k_ex).downcast_ty::<vir::Perm>(),
                        vcx.mk_map_lookup_expr(m, k_ex).downcast_ty::<vir::Perm>(),
                    );
                    let forall = vcx.mk_forall_expr(
                        vcx.alloc_slice(&[a.as_dyn(), b.as_dyn(), k.as_dyn()]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[app.as_dyn(), in_dom.as_dyn()])]),
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::Implies,
                            in_dom,
                            vcx.mk_conj(&[in_result, eq]),
                        )
                        .downcast_ty(),
                    );
                    axioms.push(vcx.mk_domain_axiom(
                        vir::vir_format_identifier!(vcx, "ax_{name}_{side}"),
                        forall,
                    ));
                };
                lookup_ax(a_ex, "left");
                lookup_ax(b_ex, "right");
                // The same facts, goal-directed: a permission check over a
                // QP chunk mentions `k in domain(f(a, b))` and `f(a, b)[k]`
                // for the checked key without any `k in domain(m)` term.
                // forall a, b, k :: { k in domain(f(a, b)) }
                //   k in domain(f(a, b)) == (k in domain(a) || k in domain(b))
                // forall a, b, k :: { f(a, b)[k] }
                //   (k in domain(a) ==> f(a, b)[k] == a[k]) &&
                //   (k in domain(b) ==> f(a, b)[k] == b[k])
                {
                    let in_a = vcx.mk_set_in_expr(k_ex, dom(a_ex));
                    let in_b = vcx.mk_set_in_expr(k_ex, dom(b_ex));
                    let in_result = vcx.mk_set_in_expr(k_ex, dom(app));
                    let lookup = vcx.mk_map_lookup_expr(app, k_ex).downcast_ty::<vir::Perm>();
                    let value_of = |in_m: vir::ExprBool<'vir>, m: vir::ExprMap<'vir>| {
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::Implies,
                            in_m,
                            vcx.mk_eq_expr(
                                lookup,
                                vcx.mk_map_lookup_expr(m, k_ex).downcast_ty::<vir::Perm>(),
                            ),
                        )
                        .downcast_ty()
                    };
                    let qvars = vcx.alloc_slice(&[a.as_dyn(), b.as_dyn(), k.as_dyn()]);
                    axioms.push(
                        vcx.mk_domain_axiom(
                            vir::vir_format_identifier!(vcx, "ax_{name}_member"),
                            vcx.mk_forall_expr(
                                qvars,
                                vcx.alloc_slice(&[vcx.mk_trigger(&[in_result])]),
                                vcx.mk_eq_expr(
                                    in_result,
                                    vcx.mk_bin_op_expr(vir::BinOpKind::Or, in_a, in_b)
                                        .downcast_ty(),
                                ),
                            ),
                        ),
                    );
                    axioms.push(vcx.mk_domain_axiom(
                        vir::vir_format_identifier!(vcx, "ax_{name}_value"),
                        vcx.mk_forall_expr(
                            qvars,
                            vcx.alloc_slice(&[vcx.mk_trigger(&[lookup])]),
                            vcx.mk_conj(&[value_of(in_a, a_ex), value_of(in_b, b_ex)]),
                        ),
                    ));
                }
                // The union of nonnegative maps is nonnegative (assumed, like
                // the nonnegativity posts on the `_IM_N` functions):
                // forall a, b, k :: { k in domain(f(a, b)) }
                //   k in domain(f(a, b)) ==> f(a, b)[k] >= none
                let in_app = vcx.mk_set_in_expr(k_ex, dom(app));
                let nonneg = vcx.mk_forall_expr(
                    vcx.alloc_slice(&[a.as_dyn(), b.as_dyn(), k.as_dyn()]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[in_app])]),
                    vcx.mk_bin_op_expr(
                        vir::BinOpKind::Implies,
                        in_app,
                        vcx.mk_bin_op_expr(
                            vir::BinOpKind::PermGeCmp,
                            vcx.mk_map_lookup_expr(app, k_ex).downcast_ty::<vir::Perm>(),
                            no_perm(vcx),
                        )
                        .downcast_ty(),
                    )
                    .downcast_ty(),
                );
                axioms.push(
                    vcx.mk_domain_axiom(
                        vir::vir_format_identifier!(vcx, "ax_{name}_nonneg"),
                        nonneg,
                    ),
                );
                if disjoint {
                    // The (assumed) domain disjointness:
                    // forall a, b, k :: { f(a, b), k in domain(a) }
                    //   k in domain(a) ==> !(k in domain(b))
                    let in_a = vcx.mk_set_in_expr(k_ex, dom(a_ex));
                    let not_in_b = vcx
                        .mk_unary_op_expr(
                            vir::UnOpKind::Not,
                            vcx.mk_set_in_expr(k_ex, dom(b_ex)).upcast_ty(),
                        )
                        .downcast_ty();
                    let forall = vcx.mk_forall_expr(
                        vcx.alloc_slice(&[a.as_dyn(), b.as_dyn(), k.as_dyn()]),
                        vcx.alloc_slice(&[vcx.mk_trigger(&[app.as_dyn(), in_a.as_dyn()])]),
                        vcx.mk_bin_op_expr(vir::BinOpKind::Implies, in_a, not_in_b)
                            .downcast_ty(),
                    );
                    axioms.push(vcx.mk_domain_axiom(
                        vir::vir_format_identifier!(vcx, "ax_{name}_disjoint"),
                        forall,
                    ));
                }
                idn
            };
            let disjoint = build("im_map_union_disjoint", true);
            let shared = build("im_map_union_shared", false);
            deps.emit_output_ref((), ())?;
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("def_im_map_union"),
                &[],
                vcx.alloc_slice(&axioms),
                vcx.alloc_slice(&funcs),
                None,
            );
            Ok((domain, MapUnionFns { disjoint, shared }))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}

/// The canonical map-shrinking function `im_map_restrict(m, keys)`: the IM-QP
/// `Map` snapshot `m` restricted to exactly `keys` (entries outside `m`'s
/// domain get the canonical `im_snap_default` value). Every `#[pure_unstable]`
/// call passes the minimal map restricted to the keys reachable from its
/// arguments.
pub(crate) struct MapRestrictEnc;

pub(crate) type MapRestrictFn<'vir> = vir::FunctionIdn<'vir, (vir::Map, vir::Set), vir::Map>;
pub(crate) type SnapDefaultFn<'vir> = vir::FunctionIdn<'vir, vir::Pair, vir::PSnap>;

#[derive(Debug, Clone, Copy)]
pub(crate) struct MapRestrictFns<'vir> {
    pub(crate) restrict: MapRestrictFn<'vir>,
    /// The canonical (arbitrary but deterministic) snapshot of a key: the
    /// value of restricted-in entries outside the source map's domain, and of
    /// `qp_to_map` entries without a positive permission.
    pub(crate) default: SnapDefaultFn<'vir>,
}

impl TaskEncoder for MapRestrictEnc {
    task_encoder::encoder_cache!(MapRestrictEnc);
    const ENCODER_NAME: &'static str = "interior mutability map restrict encoder";
    type TaskDescription<'vir> = ();
    type OutputFullDependency<'vir> = MapRestrictFns<'vir>;
    type OutputFullLocal<'vir> = vir::Domain<'vir>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        _task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        let tys = ImTys::new(deps);
        vir::with_vcx(|vcx| {
            // Both are DOMAIN functions with flat axioms: Silicon silently
            // drops a domain axiom that mentions a (non-domain) Viper
            // function, which is what the canonicity axiom must do.
            let key_set = vcx.mk_ty_set(tys.key.ty);
            let default: SnapDefaultFn<'vir> = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "im_snap_default"),
                tys.key.ty,
                vir::TYPE_PSNAP,
            );
            let restrict: MapRestrictFn<'vir> = vir::FunctionIdn::new(
                vir::vir_format_identifier!(vcx, "im_map_restrict"),
                (tys.snap_map, key_set),
                tys.snap_map,
            );
            deps.emit_output_ref((), ())?;

            let funcs = [
                vcx.mk_domain_function(default, false, None),
                vcx.mk_domain_function(restrict, false, None),
            ];

            let m = vcx.mk_local_decl("m", tys.snap_map);
            let keys = vcx.mk_local_decl("keys", key_set);
            let m_ex = vcx.mk_local_ex(m);
            let keys_ex = vcx.mk_local_ex(keys);
            let app = restrict.call()(m_ex, keys_ex);
            // forall m, keys :: { restrict(m, keys) }
            //   domain(restrict(m, keys)) == keys
            let dom_axiom = vcx.mk_domain_axiom(
                vir::ViperIdent::new("ax_im_map_restrict_dom"),
                vcx.mk_forall_expr(
                    vcx.alloc_slice(&[m.as_dyn(), keys.as_dyn()]),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[app])]),
                    vcx.mk_eq_expr(vcx.mk_map_domain_expr(app), keys_ex),
                ),
            );
            // forall m, keys, k :: { restrict(m, keys)[k] } { restrict(m, keys), k in keys }
            //   k in keys ==>
            //   restrict(m, keys)[k] == (k in domain(m) ? m[k] : im_snap_default(k))
            let entry_axiom = {
                let k = vcx.mk_local_decl("k", tys.key.ty);
                let k_ex = vcx.mk_local_ex(k);
                let in_keys = vcx.mk_set_in_expr(k_ex, keys_ex);
                let in_dom = vcx.mk_set_in_expr(k_ex, vcx.mk_map_domain_expr(m_ex));
                let value = vcx.mk_ternary_expr(
                    in_dom,
                    vcx.mk_map_lookup_expr(m_ex, k_ex)
                        .downcast_ty::<vir::PSnap>(),
                    default.call()(k_ex),
                );
                let lookup = vcx
                    .mk_map_lookup_expr(app, k_ex)
                    .downcast_ty::<vir::PSnap>();
                let eq = vcx.mk_eq_expr(lookup, value);
                vcx.mk_domain_axiom(
                    vir::ViperIdent::new("ax_im_map_restrict_entry"),
                    vcx.mk_forall_expr(
                        vcx.alloc_slice(&[m.as_dyn(), keys.as_dyn(), k.as_dyn()]),
                        vcx.alloc_slice(&[
                            vcx.mk_trigger(&[lookup.as_dyn()]),
                            vcx.mk_trigger(&[app.as_dyn(), in_keys.as_dyn()]),
                        ]),
                        vcx.mk_bin_op_expr(vir::BinOpKind::Implies, in_keys, eq)
                            .downcast_ty(),
                    ),
                )
            };

            // There is deliberately no axiom equating two restrictions of
            // pointwise-equal maps: results of `#[pure_unstable]` functions
            // are related by unfolding them down to `im_deref` lookups (and
            // from there to heap values), not by equating their map
            // arguments. Such an axiom needs a trigger on pairs of
            // applications and a nested quantifier, i.e. a case split with a
            // skolem witness per pair, which every check then pays for.
            let domain = vcx.mk_domain(
                vir::ViperIdent::new("def_im_map_restrict"),
                &[],
                vcx.alloc_slice(&[dom_axiom, entry_axiom]),
                vcx.alloc_slice(&funcs),
                None,
            );
            Ok((domain, MapRestrictFns { restrict, default }))
        })
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        for domain in Self::all_outputs_local_no_errors(program) {
            program.add_domain(domain);
        }
    }
}

/// The abstract function materializing an IM QP into its `Map` snapshot.
/// `qp_to_map(m)` requires the permission the QP over `m` grants (which is how
/// applications are discharged from the held QP), and its postcondition
/// axiomatises the result: for each key with positive permission, the result
/// holds the generic snapshot of the object at that key's address; entries
/// without a positive permission hold the canonical `im_snap_default` value,
/// so that two same-state materializations of value-equal maps agree on every
/// entry (which the `im_map_restrict` canonicity axiom depends on).
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
        let default = deps.require_dep::<MapRestrictEnc>(())?.default;

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
            let amount = vcx
                .mk_map_lookup_expr(m_ex, k_ex)
                .downcast_ty::<vir::Perm>();
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
            // ensures: forall k :: { k in domain(m) }
            //   k in domain(m) && none >= m[k] ==> result[k] == im_snap_default(k)
            // (no permission to read a snapshot; the canonical default keeps
            // the result fully determined by the map's value and the state).
            let no_amount = vcx
                .mk_bin_op_expr(vir::BinOpKind::PermGeCmp, no_perm(vcx), amount)
                .downcast_ty();
            let default_post = vcx.mk_forall_expr(
                vcx.alloc_slice(&[k]),
                vcx.alloc_slice(&[vcx.mk_trigger(&[in_dom])]),
                vcx.mk_bin_op_expr(
                    vir::BinOpKind::Implies,
                    vcx.mk_conj(&[in_dom, no_amount]),
                    vcx.mk_eq_expr(lookup, default.call()(k_ex)),
                )
                .downcast_ty(),
            );

            let func = vcx.mk_function(
                idn,
                (m,),
                vcx.alloc_slice(&[pre]),
                vcx.alloc_slice(&[dom_post, entry_post, default_post]),
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
