use crate::encoders::{
    FunctionCallEnc, MirLocalDefEnc, MirLocalDefEncOutput, MirLocalDefEncTask, ViperTupleEnc,
    mir_fn::{CallTaskDescription, RustSignature},
    mir_shared::PureRvalueEnc,
    ty::{
        RustTyDecomposition,
        generics::GParams,
        interpretation::real::TyRealLocal,
        use_pure::{TyUsePure, TyUsePureEnc},
    },
};
use pcg::utils::Place;
use prusti_interface::{
    PrustiError,
    environment::EnvQuery,
    specs::{specifications::SpecQuery, typed::ExternSpecKind},
};
use prusti_rustc_interface::{
    abi,
    data_structures::graph,
    index::IndexVec,
    middle::{
        mir,
        ty::{self, Binder, FnSig, Region, TyKind},
    },
    span::{Span, def_id::DefId, source_map::Spanned},
};
use std::{collections::HashMap, fmt};
use task_encoder::{EncodeFullError, EncodeFullResult, TaskEncoder, TaskEncoderDependencies};
use vir::{CastType, CompType, add_debug_note};

pub struct MirPureEnc;

#[derive(Clone, Debug)]
pub enum MirPureEncError {
    // UnsupportedStatement,
    // UnsupportedTerminator,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Mode {
    Old,
    Rel(usize),
    BeforeExpiry,
}

// TODO: does this need to be `&'vir [..]`?
type ExprInput<'vir> = (DefId, &'vir [vir::ExprSnap<'vir>]);
type ExprRet<'vir> = vir::ExprGenSnap<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;
type ExprRetRef<'vir> = vir::ExprGenRef<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>;
type ExprRetAny<'vir, T> = vir::ExprGen<'vir, ExprInput<'vir>, vir::ExprKind<'vir>, T>;

#[derive(Clone, Debug)]
pub struct MirPureEncOutput<'vir> {
    // TODO: is this a good place for argument types?
    //pub arg_tys: &'vir [Type<'vir>],
    pub expr: ExprRet<'vir>,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash)]
pub enum PureKind {
    Closure,
    Spec(Option<ExternSpecKind>),
    Pure,
    Constant(mir::Promoted),
}

impl PureKind {
    fn extern_spec(&self) -> Option<ExternSpecKind> {
        match self {
            PureKind::Spec(Some(kind)) => Some(*kind),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct MirPureEncTask<'vir> {
    // TODO: depth of encoding should be in the lazy context rather than here;
    //   can we integrate the lazy context into the identifier system?
    pub encoding_depth: usize,
    pub kind: PureKind,
    pub parent_def_id: DefId,             // ID of the function
    pub param_env: ty::ParamEnv<'vir>,    // param environment at the usage site
    pub substs: ty::GenericArgsRef<'vir>, // type substitutions at the usage site
    pub caller_def_id: Option<DefId>,     // ID of the caller function, if any
}

impl TaskEncoder for MirPureEnc {
    task_encoder::encoder_cache!(MirPureEnc);

    type TaskDescription<'vir> = MirPureEncTask<'vir>;

    type TaskKey<'vir> = (
        usize,                    // encoding depth
        PureKind,                 // encoding a pure function?
        DefId,                    // ID of the function
        ty::GenericArgsRef<'vir>, // ? this should be the "signature", after applying the env/substs
        Option<DefId>,            // Caller/Use DefID
    );

    type OutputFullDependency<'vir> = MirPureEncOutput<'vir>;

    type EncodingError = MirPureEncError;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        (
            // TODO
            task.encoding_depth,
            task.kind,
            task.parent_def_id,
            task.substs,
            task.caller_def_id,
        )
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut TaskEncoderDependencies<'vir, Self>,
    ) -> EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;

        let (_, kind, def_id, substs, caller_def_id) = *task_key;

        tracing::debug!("encoding {def_id:?}");
        let expr = vir::with_vcx(move |vcx| {
            let body = match kind {
                PureKind::Closure => vcx
                    .body_mut()
                    .get_closure_body(def_id, substs, caller_def_id),
                PureKind::Spec(_) => vcx.body_mut().get_spec_body(def_id, substs, caller_def_id),
                PureKind::Pure => vcx
                    .body_mut()
                    .get_pure_fn_body(def_id, substs, caller_def_id),
                PureKind::Constant(promoted) => {
                    vcx.body_mut().get_promoted_constant_body(def_id, promoted)
                }
            };

            let expr_inner = Enc::new(vcx, task_key.0, def_id, kind, &body, deps).encode_body()?;

            // We wrap the expression with an additional lazy that will perform
            // some sanity checks. These requirements cannot be expressed using
            // only the type system.
            let ret = RustTyDecomposition::from_ty(body.return_ty(), def_id);
            let expr = vcx.mk_lazy_expr(
                vir::vir_format!(vcx, "pure body {def_id:?}"),
                deps.require_ref::<TyUsePureEnc>(ret)?.snapshot,
                Box::new(move |vcx, lctx: ExprInput<'_>| {
                    // check: are we actually providing arguments for the
                    //   correct `DefId`?
                    assert_eq!(lctx.0, def_id);

                    // check: are we providing the expected number of arguments?
                    assert_eq!(lctx.1.len(), body.arg_count);

                    use vir::Reify;
                    expr_inner.kind.reify(vcx, lctx)
                }),
            );
            add_debug_note!(expr.debug_info, "Inner expr: {}", expr_inner.debug_info);
            Ok(expr)
        })?;
        tracing::debug!("finished {def_id:?}");

        Ok(((), MirPureEncOutput { expr }))
    }
}

#[derive(Debug, Default)]
struct Update<'vir> {
    binds: Vec<UpdateBind<'vir>>,
    versions: HashMap<mir::Local, Version<'vir>>,
}

#[derive(Debug)]
enum UpdateBind<'vir> {
    Local(#[allow(dead_code)] mir::Local, Version<'vir>, ExprRet<'vir>),
    Phi(Version<'vir>, ExprRet<'vir>),
}

impl<'vir> Update<'vir> {
    fn new() -> Self {
        Self::default()
    }

    fn mk_local(
        vcx: &'vir vir::VirCtxt<'vir>,
        encoding_depth: usize,
        local: mir::Local,
        version: Version<'vir>,
    ) -> &'vir str {
        vir::vir_format!(vcx, "_{}_{}s_{}", encoding_depth, local.as_usize(), version)
    }

    fn assign(
        &mut self,
        vcx: &'vir vir::VirCtxt<'vir>,
        encoding_depth: usize,
        local: mir::Local,
        mut version: Version<'vir>,
        expr: ExprRet<'vir>,
    ) {
        let decl = vcx.mk_local_decl(
            Self::mk_local(vcx, encoding_depth, local, version),
            expr.ty(),
        );
        version.initialised = Some(decl);
        self.binds.push(UpdateBind::Local(local, version, expr));
        self.versions.insert(local, version);
    }

    fn merge(self, newer: Option<Self>) -> Option<Self> {
        Some(self.merge_inner(newer?))
    }

    fn merge_inner(self, newer: Self) -> Self {
        Self {
            binds: self.binds.into_iter().chain(newer.binds).collect(),
            versions: self.versions.into_iter().chain(newer.versions).collect(),
        }
    }

    fn add_to_map(&self, curr_ver: &mut HashMap<mir::Local, Version<'vir>>) {
        for (local, ver) in &self.versions {
            curr_ver.insert(*local, *ver);
        }
    }
}

struct Enc<'vir: 'enc, 'enc> {
    vcx: &'vir vir::VirCtxt<'vir>,
    encoding_depth: usize,
    def_id: DefId,
    context: GParams<'vir>,
    body: &'enc mir::Body<'vir>,
    rev_doms: rev_doms::ReverseDominators,
    deps: &'enc mut TaskEncoderDependencies<'vir, MirPureEnc>,
    /// Always holds the next version to be used for a local.
    version_ctr: IndexVec<mir::Local, usize>,
    phi_ctr: usize,
    old_mode: bool,
    rel0_mode: bool,
    rel1_mode: bool,
    before_expiry_mode: bool,
    local_defs: MirLocalDefEncOutput<'vir>,
    impure_context: bool,
}

struct EncodedPlace<'vir> {
    snap: ExprRet<'vir>,
    place_ref: Option<ExprRetRef<'vir>>,
}

impl<'vir> EncodedPlace<'vir> {
    fn new(expr: ExprRet<'vir>, place_ref: Option<ExprRetRef<'vir>>) -> Self {
        Self {
            snap: expr,
            place_ref,
        }
    }
}

impl<'vir: 'enc, 'enc> PureRvalueEnc<'vir> for Enc<'vir, 'enc> {
    type Encoder = MirPureEnc;
    type EncodePlaceCtxt = HashMap<mir::Local, Version<'vir>>;
    type ExprCurr = ExprInput<'vir>;
    type ExprNext = vir::ExprKind<'vir>;
    fn def_id(&self) -> DefId {
        self.def_id
    }
    fn deps(&mut self) -> &mut TaskEncoderDependencies<'vir, Self::Encoder> {
        self.deps
    }
    fn vcx(&self) -> &'vir vir::VirCtxt<'vir> {
        self.vcx
    }
    fn body(&self) -> &mir::Body<'vir> {
        self.body
    }
    fn ty_use_pure(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        self.ty_use(ty)
    }

    fn encode_place_snap<'slf>(
        &mut self,
        place: Place<'vir>,
        curr_ver: &Self::EncodePlaceCtxt,
    ) -> ExprRet<'vir> {
        self.encode_place_with_ref(curr_ver, place).snap
    }

    fn encode_operand_snap(
        &mut self,
        operand: &mir::Operand<'vir>,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
    ) -> Result<ExprRet<'vir>, EncodeFullError<'vir, Self::Encoder>> {
        Ok(match operand {
            mir::Operand::Copy(place) | mir::Operand::Move(place) => {
                self.encode_place_snap((*place).into(), curr_ver)
            }
            mir::Operand::Constant(box constant) => {
                self.encode_constant_snap(constant)?.upcast_ty().lift()
            }
        })
    }
}

impl<'vir: 'enc, 'enc> Enc<'vir, 'enc> {
    fn new(
        vcx: &'vir vir::VirCtxt<'vir>,
        encoding_depth: usize,
        def_id: DefId,
        kind: PureKind,
        body: &'enc mir::Body<'vir>,
        deps: &'enc mut TaskEncoderDependencies<'vir, MirPureEnc>,
    ) -> Self {
        assert!(
            !graph::is_cyclic(&body.basic_blocks),
            "MIR pure encoding does not support loops"
        );
        let rev_doms = rev_doms::ReverseDominators::new(&body.basic_blocks);
        let local_def_enc_task = if kind.extern_spec().is_some() {
            MirLocalDefEncTask::ExternSpec(def_id)
        } else {
            MirLocalDefEncTask::Local {
                def_id,
                all_locals: true,
            }
        };
        let local_defs = deps
            .require_dep::<MirLocalDefEnc>(local_def_enc_task)
            .unwrap();
        Self {
            vcx,
            encoding_depth,
            def_id,
            context: GParams::new_maybe_extern(def_id, kind.extern_spec()),
            body,
            rev_doms,
            deps,
            // visited: IndexVec::from_elem_n(false, body.basic_blocks.len()),
            version_ctr: IndexVec::from_elem_n(0, body.local_decls.len()),
            phi_ctr: 0,
            old_mode: false,
            rel0_mode: false,
            rel1_mode: false,
            before_expiry_mode: false,
            local_defs,
            impure_context: matches!(kind, PureKind::Spec(_)),
        }
    }

    fn ty_use(&mut self, ty: ty::Ty<'vir>) -> TyUsePure<'vir> {
        let ty_task = RustTyDecomposition::from_ty(ty, self.context);
        self.deps.require_dep::<TyUsePureEnc>(ty_task).unwrap()
    }

    fn ty_use_real(&mut self) -> &'vir TyRealLocal<'vir> {
        let ty_task = RustTyDecomposition::from_real();
        self.deps
            .require_dep::<TyUsePureEnc>(ty_task)
            .unwrap()
            .expect_builtin()
            .expect_real()
    }

    fn get_ty_for_local(&mut self, local: mir::Local) -> vir::TypeSnap<'vir> {
        let ty = self.body.local_decls[local].ty;
        let ty_task = RustTyDecomposition::from_ty(ty, self.context);
        self.deps
            .require_ref::<TyUsePureEnc>(ty_task)
            .unwrap()
            .snapshot
    }

    fn mk_local_ex(&mut self, _local: mir::Local, version: Version<'vir>) -> ExprRet<'vir> {
        self.vcx.mk_local_ex(version.initialised.unwrap())
    }

    fn mk_phi(&self, version: Version<'vir>) -> &'vir str {
        vir::vir_format!(self.vcx, "_{}_phi_{}", self.encoding_depth, version)
    }

    fn mk_phi_acc<T: vir::CompType>(
        &mut self,
        tuple_ref: &crate::encoders::ViperTupleEncOutput<'vir>,
        phi_idx: Version<'vir>,
        elem_idx: usize,
        _ty: vir::Type<'vir, T>,
    ) -> ExprRet<'vir> {
        tuple_ref.mk_elem(
            self.vcx,
            self.vcx.mk_local_ex(phi_idx.initialised.unwrap()),
            elem_idx,
        )
    }

    fn bump_version(
        &mut self,
        update: &mut Update<'vir>,
        local: mir::Local,
        expr: ExprRet<'vir>,
        location: mir::Location,
    ) {
        let new_version = self.bump_version_no_assign(local, location);
        // check that `local` and `expr` type correspond
        update.assign(self.vcx, self.encoding_depth, local, new_version, expr);
    }

    fn bump_version_no_assign(
        &mut self,
        local: mir::Local,
        location: mir::Location,
    ) -> Version<'vir> {
        let index = self.version_ctr[local];
        self.version_ctr[local] += 1;
        Version {
            index,
            location,
            initialised: None,
        }
    }

    fn reify_binds<T: CompType>(
        &self,
        update: Update<'vir>,
        expr: ExprRetAny<'vir, T>,
    ) -> ExprRetAny<'vir, T> {
        update.binds.iter().rfold(expr, |expr, bind| match bind {
            UpdateBind::Local(_, version, val) => {
                let decl = version.initialised.unwrap();
                self.vcx.mk_let_expr(decl, val, expr)
            }
            UpdateBind::Phi(version, val) => {
                self.vcx
                    .mk_let_expr(version.initialised.unwrap(), val, expr)
            }
        })
    }

    fn reify_branch(
        &mut self,
        tuple_ref: &crate::encoders::ViperTupleEncOutput<'vir>,
        mod_locals: &[mir::Local],
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        update: Option<Update<'vir>>,
    ) -> ExprRet<'vir> {
        update
            .map(|update| {
                let tuple_args = mod_locals
                    .iter()
                    .map(|local| {
                        let version = update.versions.get(local).copied().unwrap_or_else(|| {
                            // TODO: remove (debug)
                            if !curr_ver.contains_key(local) {
                                tracing::error!("unknown version of local! {}", local.as_usize());
                                return Version {
                                    index: 0xff,
                                    ..Default::default()
                                };
                            }
                            curr_ver[local]
                        });

                        self.mk_local_ex(*local, version)
                    })
                    .collect::<Vec<_>>();
                self.reify_binds(update, tuple_ref.mk_cons(self.vcx, tuple_args))
            })
            .unwrap_or_else(|| tuple_ref.mk_unreachable(self.vcx))
    }

    fn encode_body(&mut self) -> Result<ExprRet<'vir>, EncodeFullError<'vir, MirPureEnc>> {
        let mut init = Update::new();
        let v0 = Version::default();
        // TODO: what about locals which never have StorageLive (i.e. always_live)?
        init.versions.insert(mir::RETURN_PLACE, v0);
        for local in 1..=self.body.arg_count {
            let local_ex = self.vcx.mk_lazy_expr(
                vir::vir_format!(self.vcx, "pure in _{local}"),
                self.get_ty_for_local(local.into()),
                Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[local - 1].kind),
            );
            // check that `local` and `expr` type correspond
            self.bump_version(&mut init, local.into(), local_ex, v0.location);
        }

        let update = self.encode_cfg(&init.versions, mir::START_BLOCK, self.rev_doms.end)?;

        // do we ever panic here? if yes, return the `unreachable_to_snap` expr.
        let res = init
            .merge(update)
            .expect("function unconditionally terminates with unreachable");
        let ret_version = res.versions.get(&mir::RETURN_PLACE).copied().unwrap_or(v0);

        let ex = self.mk_local_ex(mir::RETURN_PLACE, ret_version);
        Ok(self.reify_binds(res, ex))
    }

    fn encode_cfg(
        &mut self,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        curr: mir::BasicBlock,
        join_point: mir::BasicBlock,
    ) -> Result<Option<Update<'vir>>, EncodeFullError<'vir, MirPureEnc>> {
        if curr == join_point {
            // We are done with the current fragment of the CFG, the rest is
            // handled in a parent call.
            return Ok(Some(Update::new()));
        }

        // walk block statements first
        let mut new_curr_ver = curr_ver.clone();
        let mut stmt_update = Update::new();
        for (statement_index, stmt) in self.body[curr].statements.iter().enumerate() {
            let location = mir::Location {
                block: curr,
                statement_index,
            };
            let newer = self.encode_stmt(&new_curr_ver, stmt, location)?;
            newer.add_to_map(&mut new_curr_ver);
            stmt_update = stmt_update.merge_inner(newer);
        }

        // then walk terminator
        let term = self.body[curr].terminator.as_ref().unwrap();
        let location = mir::Location {
            block: curr,
            statement_index: self.body[curr].statements.len(),
        };
        match &term.kind {
            &mir::TerminatorKind::Goto { target }
            | &mir::TerminatorKind::FalseEdge {
                real_target: target,
                ..
            }
            | &mir::TerminatorKind::Drop { target, .. } => {
                let rest_update = self.encode_cfg(&new_curr_ver, target, join_point)?;
                Ok(stmt_update.merge(rest_update))
            }

            mir::TerminatorKind::SwitchInt { discr, targets } => {
                // encode the discriminant operand
                let discr_expr = self
                    .encode_operand_snap(discr, &new_curr_ver)?
                    .downcast_ty();
                let discr_ty = discr.ty(self.body, self.vcx.tcx());
                let discr_ty_out = self.ty_use(discr_ty).expect_primitive();

                // walk `curr` -> `targets[i]` -> `join` for each target. The
                // join point the bb which is an immediate reverse dominator of
                // the branch point.
                // TODO: indexvec?
                let new_join_point = self.rev_doms.immediate_dominator(curr);
                let mut updates = targets
                    .all_targets()
                    .iter()
                    .map(|target| self.encode_cfg(&new_curr_ver, *target, new_join_point))
                    .collect::<Result<Vec<_>, _>>()?;

                // find locals updated in any of the results, which were also
                // defined before the branch
                let mut mod_locals = updates
                    .iter()
                    .flat_map(|update| update.iter().flat_map(|v| v.versions.keys()))
                    .filter(|local| new_curr_ver.contains_key(local))
                    .copied()
                    .collect::<Vec<_>>();
                mod_locals.sort();
                mod_locals.dedup();
                let mod_tys = mod_locals
                    .iter()
                    .map(|l| self.body.local_decls[*l].ty)
                    .collect();

                // for each branch, create a Viper tuple of the updated locals
                let tuple_ref = self
                    .deps
                    .require_dep::<ViperTupleEnc>((self.def_id, mod_tys))
                    .unwrap();
                let otherwise_update = updates.pop().unwrap();
                let phi_expr = targets.iter().zip(updates).fold(
                    self.reify_branch(&tuple_ref, &mod_locals, &new_curr_ver, otherwise_update),
                    |expr, ((cond_val, _target), branch_update)| {
                        self.vcx.mk_ternary_expr(
                            self.vcx.mk_eq_expr(
                                discr_ty_out.expect_native().snap_to_prim.call()(discr_expr),
                                discr_ty_out.expr_from_bits(discr_ty, cond_val).lift(),
                            ),
                            self.reify_branch(
                                &tuple_ref,
                                &mod_locals,
                                &new_curr_ver,
                                branch_update,
                            ),
                            expr,
                        )
                    },
                );

                // assign tuple into a `phi` variable
                let mut phi_idx = Version {
                    index: self.phi_ctr,
                    location,
                    initialised: None,
                };
                phi_idx.initialised = Some(
                    self.vcx
                        .mk_local_decl(self.mk_phi(phi_idx), tuple_ref.snapshot()),
                );
                self.phi_ctr += 1;
                let mut phi_update = Update::new();
                phi_update.binds.push(UpdateBind::Phi(phi_idx, phi_expr));

                // update locals by destructuring `phi` variable
                // TODO: maybe this is unnecessary, we could instead use tuple
                //   access directly instead of the locals going forward?
                for (elem_idx, local) in mod_locals.iter().enumerate() {
                    let ty = self.get_ty_for_local(*local);
                    let expr = self.mk_phi_acc(&tuple_ref, phi_idx, elem_idx, ty);
                    self.bump_version(&mut phi_update, *local, expr, location);
                    new_curr_ver.insert(*local, phi_update.versions[local]);
                }

                // walk `join` -> `end`
                let end_update = self.encode_cfg(&new_curr_ver, new_join_point, join_point)?;
                Ok(stmt_update.merge(phi_update.merge(end_update)))
            }

            // TODO: there is some code duplication between here and SwitchInt
            mir::TerminatorKind::Assert {
                cond,
                expected,
                target,
                ..
            } => {
                // encode the condition operand
                let cond_ty = cond.ty(self.body, self.vcx.tcx());
                assert_eq!(*cond_ty.kind(), ty::TyKind::Bool);
                let cond_expr = self.encode_operand_snap(cond, &new_curr_ver)?.downcast_ty();
                let cond_ty_out = self.ty_use(cond_ty).expect_primitive();

                // if cond == expected: walk the rest of the CFG
                let ok_update = self.encode_cfg(&new_curr_ver, *target, join_point)?;

                // find locals updated in the "ok" branch, which were also
                // defined before the branch
                // TODO: is the unwrap here ok? can ok_update also be None?
                let mut mod_locals = ok_update
                    .as_ref()
                    .unwrap()
                    .versions
                    .keys()
                    .filter(|local| new_curr_ver.contains_key(local))
                    .copied()
                    .collect::<Vec<_>>();
                mod_locals.sort();
                mod_locals.dedup();
                let mod_tys = mod_locals
                    .iter()
                    .map(|l| self.body.local_decls[*l].ty)
                    .collect();

                // create a Viper tuple of the updated locals
                let tuple_ref = self
                    .deps
                    .require_dep::<ViperTupleEnc>((self.def_id, mod_tys))
                    .unwrap();
                let phi_expr = self.vcx.mk_ternary_expr(
                    self.vcx.mk_eq_expr(
                        cond_ty_out.expect_native().snap_to_prim.call()(cond_expr),
                        cond_ty_out
                            .expr_from_bits(cond_ty, if *expected { 1 } else { 0 })
                            .lift(),
                    ),
                    self.reify_branch(&tuple_ref, &mod_locals, &new_curr_ver, ok_update),
                    self.reify_branch(&tuple_ref, &mod_locals, &new_curr_ver, None),
                );

                // assign tuple into a `phi` variable
                let mut phi_idx = Version {
                    index: self.phi_ctr,
                    location,
                    initialised: None,
                };
                phi_idx.initialised = Some(
                    self.vcx
                        .mk_local_decl(self.mk_phi(phi_idx), tuple_ref.snapshot()),
                );
                self.phi_ctr += 1;
                let mut phi_update = Update::new();
                phi_update.binds.push(UpdateBind::Phi(phi_idx, phi_expr));

                // update locals by destructuring `phi` variable
                // TODO: maybe this is unnecessary, we could instead use tuple
                //   access directly instead of the locals going forward?
                for (elem_idx, local) in mod_locals.iter().enumerate() {
                    let ty = self.get_ty_for_local(*local);
                    let expr = self.mk_phi_acc(&tuple_ref, phi_idx, elem_idx, ty);
                    self.bump_version(&mut phi_update, *local, expr, location);
                    new_curr_ver.insert(*local, phi_update.versions[local]);
                }

                Ok(stmt_update.merge(Some(phi_update)))
            }

            mir::TerminatorKind::Return => Ok(Some(stmt_update)),

            mir::TerminatorKind::Unreachable => {
                // will result in generating an unreachable phi merge
                Ok(None)
            }

            mir::TerminatorKind::Call {
                func,
                args,
                destination,
                target,
                ..
            } => {
                let Some(target) = *target else {
                    // target is none if the call diverges (i.e. returns !), in
                    // this case treat it just like an unreachable terminator.
                    return Ok(None);
                };

                let func_ty = func.ty(self.body, self.vcx.tcx());
                let (def_id, arg_tys) = RustSignature::get_def_id_and_caller_substs(func_ty);
                let expr = {
                    // A fn call in pure can only be one of two kinds: a
                    // call to another pure function, or a call to a prusti
                    // builtin function.
                    let is_pure = crate::encoders::with_proc_spec(
                        SpecQuery::GetProcKind(
                            def_id,
                            ty::List::identity_for_item(self.vcx.tcx(), def_id),
                        ),
                        |def_spec| def_spec.kind.is_pure().unwrap_or_default(),
                    )
                    .unwrap_or_default();

                    let env_query = EnvQuery::new(self.vcx.tcx());
                    if env_query.is_function_in_crate(def_id, arg_tys, "prusti_contracts") {
                        let sig = self.vcx.tcx().fn_sig(def_id);
                        let sig = sig.instantiate_identity();
                        let actual_impl = env_query.find_impl_of_trait_method_call(def_id, arg_tys);
                        self.encode_prusti_builtin(
                            def_id,
                            actual_impl,
                            sig,
                            arg_tys,
                            args,
                            &new_curr_ver,
                        )
                    } else if is_pure {
                        let pure_func = self
                            .deps
                            .require_dep::<FunctionCallEnc>(CallTaskDescription::new(
                                self.context,
                                arg_tys,
                                def_id,
                            ))
                            .unwrap();
                        let snap_args = args
                            .iter()
                            .map(|arg| self.encode_operand_snap(&arg.node, &new_curr_ver))
                            .collect::<Result<Vec<_>, _>>()?;
                        Ok(pure_func.call(snap_args))
                    } else {
                        panic!("call to unknown non-pure function in pure code ({def_id:?})");
                    }
                };

                let mut term_update = Update::new();
                assert!(destination.projection.is_empty());
                self.bump_version(&mut term_update, destination.local, expr?, location);
                term_update.add_to_map(&mut new_curr_ver);

                // walk rest of CFG
                let end_update = self.encode_cfg(&new_curr_ver, target, join_point)?;

                Ok(stmt_update.merge_inner(term_update).merge(end_update))
            }

            k => todo!("terminator kind {k:?}"),
        }
    }

    fn encode_stmt(
        &mut self,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        stmt: &mir::Statement<'vir>,
        location: mir::Location,
    ) -> Result<Update<'vir>, EncodeFullError<'vir, MirPureEnc>> {
        let mut update = Update::new();
        match &stmt.kind {
            &mir::StatementKind::StorageLive(local) => {
                let new_version = self.bump_version_no_assign(local, location);
                update.versions.insert(local, new_version);
            }
            mir::StatementKind::StorageDead(..)
            | mir::StatementKind::FakeRead(..)
            | mir::StatementKind::AscribeUserType(..)
            | mir::StatementKind::PlaceMention(..) => {} // nop
            mir::StatementKind::Assign(box (dest, rvalue)) => {
                //assert!(dest.projection.is_empty());
                let span = stmt.source_info.span;
                let expr = self.encode_rvalue(curr_ver, rvalue, span)?;
                self.bump_version(&mut update, dest.local, expr, location);
            }
            k => todo!("statement kind {k:?}"),
        }
        Ok(update)
    }

    fn encode_rvalue(
        &mut self,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        rvalue: &mir::Rvalue<'vir>,
        span: Span,
    ) -> Result<ExprRet<'vir>, EncodeFullError<'vir, MirPureEnc>> {
        let rvalue_ty = rvalue.ty(self.body, self.vcx.tcx());
        match rvalue {
            mir::Rvalue::Use(op) => self.encode_operand_snap(op, curr_ver),
            mir::Rvalue::Ref(_, kind, place) => {
                let rvalue_snapshot_encoding = self.ty_use(rvalue_ty);
                let encoded_place = self.encode_place_with_ref(curr_ver, (*place).into());
                if kind.mutability().is_mut() {
                    let e_rvalue_ty = rvalue_snapshot_encoding.expect_mutref();
                    // We want to distinguish if `place` is a value that lives
                    // in pure code or not. If it lives in impure (the only way
                    // that this can happen is that we have a `&mut` argument)
                    // then we want to return the actual address in the
                    // snapshot. Otherwise we want to use `null` as this value
                    // should never escape pure code anyway. Thus `place_ref`
                    // will return `None` if this isn't a re-borrow, and if it's
                    // a re-borrow of created-in-pure reference then it will be
                    // field projections of `null` which is also `null`.
                    let place_ref = encoded_place
                        .place_ref
                        .unwrap_or_else(|| self.vcx.mk_null().lazy());
                    Ok(e_rvalue_ty
                        .prim_to_snap(place_ref, encoded_place.snap)
                        .upcast_ty())
                } else {
                    let e_rvalue_ty = rvalue_snapshot_encoding.expect_immref();
                    // For shared borrows we want to use just the snapshot
                    // without the reference so that snapshot equality compares
                    // only values.
                    Ok(e_rvalue_ty
                        .prim_to_snap(self.vcx.mk_null().lazy(), encoded_place.snap)
                        .upcast_ty())
                }
            }
            mir::Rvalue::BinaryOp(op, box (l, r)) => {
                self.encode_binop_snap(rvalue_ty, *op, l, r, curr_ver)
            }
            mir::Rvalue::UnaryOp(unop, operand) => {
                self.encode_unary_op_snap(rvalue_ty, *unop, operand, curr_ver)
            }
            mir::Rvalue::Aggregate(
                box kind @ (mir::AggregateKind::Adt(..)
                | mir::AggregateKind::Tuple
                | mir::AggregateKind::Closure(..)),
                fields,
            ) => self.encode_aggregate_snap(rvalue_ty, kind, fields, curr_ver),
            mir::Rvalue::Discriminant(place) => {
                let place_ty = place.ty(self.body, self.vcx.tcx());
                let ty = self.ty_use(place_ty.ty);
                let discr = match ty
                    .get_enumlike()
                    .filter(|_| place_ty.variant_index.is_none())
                {
                    Some(ty) => ty.snap_to_discr_snap(
                        self.encode_place_snap((*place).into(), curr_ver)
                            .downcast_ty(),
                    ),
                    None => {
                        let e_rvalue_ty = self.ty_use(rvalue_ty).expect_primitive();
                        // mir::Rvalue::Discriminant documents "Returns zero for types without discriminant"
                        let zero = self.vcx.mk_uint::<0>();
                        e_rvalue_ty.prim_to_snap.call()(zero.upcast_ty()).lift()
                    }
                };
                Ok(discr.upcast_ty())
            }
            mir::Rvalue::Cast(kind, operand, ty) => {
                Ok(self.encode_cast_snap(*kind, operand, *ty, curr_ver)?.expr)
            }
            mir::Rvalue::Len(place) => Ok(self.encode_len_snap((*place).into(), curr_ver)),
            _ => self.vcx.with_span(span, |vcx| {
                let error_msg = format!("unsupported rvalue {rvalue:?} might be reached");
                vcx.handle_error("application.precondition:assertion.false", move |_| {
                    Some(vec![PrustiError::verification(&error_msg, span.into())])
                });
                Ok(self.ty_use(rvalue_ty).unreachable_to_snap())
            }),
        }
    }

    fn encode_place_element(
        &mut self,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        place_ty: mir::PlaceTy<'vir>,
        elem: mir::PlaceElem<'vir>,
        encoded_place: EncodedPlace<'vir>,
    ) -> EncodedPlace<'vir> {
        let e_ty = self.ty_use(place_ty.ty);
        match elem {
            mir::ProjectionElem::Deref => {
                assert!(place_ty.variant_index.is_none());
                match place_ty.ty.kind() {
                    TyKind::Adt(adt, _) if adt.is_box() => {
                        let proj =
                            e_ty.expect_variant_opt(place_ty.variant_index)[abi::FieldIdx::ZERO];
                        let proj_app = proj.read(encoded_place.snap.downcast_ty());
                        let place_ref = encoded_place.place_ref.map(|pr| proj.field_ref(pr));
                        EncodedPlace::new(proj_app, place_ref)
                    }
                    TyKind::Ref(.., ty::Mutability::Not) => {
                        let e_ty = e_ty.expect_immref();
                        let val_expr = e_ty.value_access(encoded_place.snap.downcast_ty());
                        EncodedPlace::new(val_expr, encoded_place.place_ref)
                    }
                    TyKind::Ref(.., ty::Mutability::Mut) => {
                        assert!(
                            self.impure_context,
                            "mutable deref is not allowed in a pure context (e.g. pure functions)"
                        );
                        let e_ty = e_ty.expect_mutref();
                        let val_expr = e_ty.deref_access(encoded_place.snap.downcast_ty());
                        // TODO: avoid all of this by using shallow and deep snapshots
                        let ty_task = RustTyDecomposition::from_ty(place_ty.ty, self.context);
                        let inner = ty_task.ty.expect_mutref();
                        let normalized =
                            inner.decompose_compare_normalize(ty_task.ty.params, ty_task.args);
                        let caster = self
                            .deps
                            .require_dep::<crate::GArgsCastEnc<crate::Pure>>(normalized)
                            .unwrap();
                        let inner_ty_task =
                            inner.decompose_context(ty_task.ty.params, ty_task.args);
                        let inner_ty = self
                            .deps
                            .require_dep::<crate::encoders::TyUseImpureEnc>(inner_ty_task)
                            .unwrap();
                        let val_expr = inner_ty.ref_to_snap(val_expr);
                        let val_expr = caster.cast_to_caller_ctx(val_expr);
                        EncodedPlace::new(val_expr, encoded_place.place_ref)
                    }
                    _ => unreachable!(),
                }
            }
            mir::ProjectionElem::Field(field_idx, _ty) => {
                let proj = e_ty.expect_variant_opt(place_ty.variant_index)[field_idx];
                let proj_app = proj.read(encoded_place.snap.downcast_ty());
                let place_ref = encoded_place.place_ref.map(|pr| proj.field_ref(pr));
                EncodedPlace::new(proj_app, place_ref)
            }
            mir::ProjectionElem::Index(idx) => {
                let proj = e_ty.expect_array();
                let idx = self
                    .encode_place_with_ref(curr_ver, mir::Place::from(idx).into())
                    .snap;
                let usize_ty = self.ty_use(self.vcx.tcx().types.usize);
                let idx = usize_ty
                    .expect_primitive()
                    .expect_native()
                    .snap_to_prim
                    .call()(idx.downcast_ty())
                .downcast_ty();
                let proj_app = proj.index(encoded_place.snap.downcast_ty(), idx);
                let place_ref = encoded_place
                    .place_ref
                    .map(|pr| proj.ref_to_index_ref(pr, idx));
                EncodedPlace::new(proj_app, place_ref)
            }
            mir::ProjectionElem::Downcast(..) => encoded_place,
            _ => todo!("Unsupported ProjectionElem {:?}", elem),
        }
    }

    fn in_mode(&self) -> bool {
        self.old_mode || self.rel0_mode || self.rel1_mode || self.before_expiry_mode
    }

    fn encode_place_with_ref(
        &mut self,
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
        place: Place<'vir>,
    ) -> EncodedPlace<'vir> {
        // TODO: remove (debug)
        assert!(curr_ver.contains_key(&place.local));

        let mut place_ty = mir::PlaceTy::from_ty(self.body.local_decls[place.local].ty);

        let should_wrap = self.in_mode() && {
            let local_kind = self.body.local_kind(place.local);
            local_kind == mir::LocalKind::Arg || local_kind == mir::LocalKind::ReturnPointer
        };

        let expr = if should_wrap {
            let local_as_uzize = place.local.as_usize();
            self.vcx.mk_lazy_expr(
                vir::vir_format!(self.vcx, "wraped in _{}", local_as_uzize),
                self.get_ty_for_local(place.local),
                Box::new(move |_vcx, lctx: ExprInput<'vir>| lctx.1[local_as_uzize - 1].kind),
            )
        } else {
            self.mk_local_ex(place.local, curr_ver[&place.local])
        };
        let place_ref: Option<ExprRetRef<'vir>> =
            Some(self.local_defs[place.local].local_ex.lazy());
        let mut encoded_place = EncodedPlace::new(expr, place_ref);
        // TODO: factor this out (duplication with impure encoder)?
        for elem in place.projection {
            encoded_place = self.encode_place_element(curr_ver, place_ty, *elem, encoded_place);
            place_ty = place_ty.projection_ty(self.vcx.tcx(), *elem);
        }
        // Can we ever have the use of a projected place?
        assert!(place_ty.variant_index.is_none());

        if should_wrap {
            if self.old_mode {
                encoded_place.snap = self.vcx.mk_old_expr(encoded_place.snap);
            }
            if self.rel0_mode {
                encoded_place.snap = self.vcx.mk_rel_expr(encoded_place.snap, 0);
            }
            if self.rel1_mode {
                encoded_place.snap = self.vcx.mk_rel_expr(encoded_place.snap, 1);
            }
            if self.before_expiry_mode {
                encoded_place.snap = self.vcx.mk_old_lhs_expr(encoded_place.snap);
            }
        }

        encoded_place
    }

    fn encode_real_op(
        &mut self,
        bin_op: vir::BinOpKind,
        args: &[Spanned<mir::Operand<'vir>>],
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
    ) -> Result<
        vir::ExprGenCSnap<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
        EncodeFullError<'vir, MirPureEnc>,
    > {
        let real = self.ty_use_real();
        let real1 = real.snap_to_perm.call()(
            self.encode_operand_snap(&args[0].node, curr_ver)?
                .downcast_ty(),
        );
        let real2 = real.snap_to_perm.call()(
            self.encode_operand_snap(&args[1].node, curr_ver)?
                .downcast_ty(),
        );
        Ok(real.perm_to_snap.call()(
            self.vcx.mk_bin_op_expr(bin_op, real1, real2).downcast_ty(),
        ))
    }

    fn encode_real_cmp(
        &mut self,
        bin_op: vir::BinOpKind,
        args: &[Spanned<mir::Operand<'vir>>],
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
    ) -> Result<
        vir::ExprGenCSnap<'vir, ExprInput<'vir>, vir::ExprKind<'vir>>,
        EncodeFullError<'vir, MirPureEnc>,
    > {
        let real = self.ty_use_real();
        let bool = self.ty_use(self.vcx.tcx().types.bool);
        let bool = bool.expect_primitive();
        let a0_ty = args[0].node.ty(self.body, self.vcx.tcx());
        let real1 = self
            .encode_operand_snap(&args[0].node, curr_ver)?
            .downcast_ty();
        let real1_deref = real.snap_to_perm.call()(
            self.ty_use(a0_ty)
                .expect_immref()
                .value_access(real1)
                .downcast_ty(),
        );

        let a1_ty = args[1].node.ty(self.body, self.vcx.tcx());
        let real2 = self
            .encode_operand_snap(&args[1].node, curr_ver)?
            .downcast_ty();
        let real2_deref = real.snap_to_perm.call()(
            self.ty_use(a1_ty)
                .expect_immref()
                .value_access(real2)
                .downcast_ty(),
        );
        Ok(bool.prim_to_snap.call()(
            self.vcx
                .mk_bin_op_expr_inner(bin_op, real1_deref.as_dyn(), real2_deref.as_dyn())
                .downcast_ty(),
        ))
    }

    fn encode_prusti_builtin(
        &mut self,
        def_id: DefId,
        actual_impl: Option<DefId>,
        _sig: Binder<'vir, FnSig<'vir>>,
        arg_tys: ty::GenericArgsRef<'vir>,
        args: &[Spanned<mir::Operand<'vir>>],
        curr_ver: &HashMap<mir::Local, Version<'vir>>,
    ) -> Result<ExprRet<'vir>, EncodeFullError<'vir, MirPureEnc>> {
        #[derive(Debug, PartialEq, Eq)]
        enum PrustiBuiltin {
            Forall,
            Exists,
            SnapshotEquality,
            SliceLen,
            ModeStart(Mode),
            ModeEnd(Mode),
            IsNaN(ty::FloatTy),
            IsInfinite(ty::FloatTy),
            FlAbs(ty::FloatTy),
            FlToReal,
            RealMul,
            RealEq,
            RealSub,
            RealAdd,
            RealDiv,
            RealNeg,
            RealLt,
            RealLe,
            RealGt,
            RealGe,
        }

        let item_name = self.vcx.tcx().item_name(def_id);
        let env_query = EnvQuery::new(self.vcx.tcx());

        // TODO: this probably isn't necessary
        let builtin = match (
            env_query
                .find_impl_type_name(actual_impl.unwrap_or(def_id))
                .as_deref(),
            item_name.as_str(),
        ) {
            (None, "forall") => PrustiBuiltin::Forall,
            (None, "exists") => PrustiBuiltin::Exists,
            (None, "snapshot_equality") => PrustiBuiltin::SnapshotEquality,
            (None, "old_start") => PrustiBuiltin::ModeStart(Mode::Old),
            (None, "old_end") => PrustiBuiltin::ModeEnd(Mode::Old),
            (None, "rel_start") => PrustiBuiltin::ModeStart(Mode::Rel(
                arg_tys[0]
                    .expect_const()
                    .to_value()
                    .valtree
                    .try_to_scalar_int()
                    .unwrap()
                    .to_bits_unchecked() as usize,
            )),
            (None, "rel_end") => PrustiBuiltin::ModeEnd(Mode::Rel(
                arg_tys[0]
                    .expect_const()
                    .to_value()
                    .valtree
                    .try_to_scalar_int()
                    .unwrap()
                    .to_bits_unchecked() as usize,
            )),
            (None, "slice_len") => PrustiBuiltin::SliceLen,
            (None, "before_expiry_start") => PrustiBuiltin::ModeStart(Mode::BeforeExpiry),
            (None, "before_expiry_end") => PrustiBuiltin::ModeEnd(Mode::BeforeExpiry),
            (None, "f16_is_nan") => PrustiBuiltin::IsNaN(ty::FloatTy::F16),
            (None, "f32_is_nan") => PrustiBuiltin::IsNaN(ty::FloatTy::F32),
            (None, "f64_is_nan") => PrustiBuiltin::IsNaN(ty::FloatTy::F64),
            (None, "f128_is_nan") => PrustiBuiltin::IsNaN(ty::FloatTy::F128),
            (None, "f16_is_infinite") => PrustiBuiltin::IsInfinite(ty::FloatTy::F16),
            (None, "f32_is_infinite") => PrustiBuiltin::IsInfinite(ty::FloatTy::F32),
            (None, "f64_is_infinite") => PrustiBuiltin::IsInfinite(ty::FloatTy::F64),
            (None, "f128_is_infinite") => PrustiBuiltin::IsInfinite(ty::FloatTy::F128),
            (None, "f16_abs") => PrustiBuiltin::FlAbs(ty::FloatTy::F16),
            (None, "f32_abs") => PrustiBuiltin::FlAbs(ty::FloatTy::F32),
            (None, "f64_abs") => PrustiBuiltin::FlAbs(ty::FloatTy::F64),
            (None, "f128_abs") => PrustiBuiltin::FlAbs(ty::FloatTy::F128),
            (Some("prusti_contracts::Real"), "from") => PrustiBuiltin::FlToReal,
            (Some("prusti_contracts::Real"), "mul") => PrustiBuiltin::RealMul,
            (Some("prusti_contracts::Real"), "eq") => PrustiBuiltin::RealEq,
            (Some("prusti_contracts::Real"), "sub") => PrustiBuiltin::RealSub,
            (Some("prusti_contracts::Real"), "add") => PrustiBuiltin::RealAdd,
            (Some("prusti_contracts::Real"), "div") => PrustiBuiltin::RealDiv,
            (Some("prusti_contracts::Real"), "neg") => PrustiBuiltin::RealNeg,
            (Some("prusti_contracts::Real"), "lt") => PrustiBuiltin::RealLt,
            (Some("prusti_contracts::Real"), "le") => PrustiBuiltin::RealLe,
            (Some("prusti_contracts::Real"), "gt") => PrustiBuiltin::RealGt,
            (Some("prusti_contracts::Real"), "ge") => PrustiBuiltin::RealGe,
            (_, other) => panic!("illegal prusti::builtin ({other})"),
        };

        let bool = self.ty_use(self.vcx.tcx().types.bool);
        let bool = bool.expect_primitive();
        let mk_bool =
            |prim: vir::ExprGenBool<'vir, _, _>| bool.prim_to_snap.call()(prim.upcast_ty());
        Ok(match builtin {
            PrustiBuiltin::SnapshotEquality => {
                assert_eq!(args.len(), 2);
                let lhs = self.encode_operand_snap(&args[0].node, curr_ver)?;
                let rhs = self.encode_operand_snap(&args[1].node, curr_ver)?;
                mk_bool(self.vcx.mk_eq_expr(lhs, rhs))
            }
            PrustiBuiltin::Forall | PrustiBuiltin::Exists => {
                assert_eq!(arg_tys.len(), 3);

                let encoded_args = args
                    .iter()
                    .map(|oper| self.encode_operand_snap(&oper.node, curr_ver))
                    .collect::<Result<Vec<_>, _>>()?;
                // TODO: for now, let's expect this to give us these two:
                //   - expression for the triggers
                //   - expression for the body
                assert_eq!(encoded_args.len(), 2);

                let closure_ty = arg_tys[2].expect_ty();

                let (qvar_tys, _upvar_tys, cl_kind, cl_def_id) = match closure_ty.kind() {
                    TyKind::Closure(cl_def_id, cl_args) => (
                        match cl_args.as_closure().sig().skip_binder().inputs()[0].kind() {
                            TyKind::Tuple(list) => list,
                            _ => unreachable!(),
                        },
                        cl_args.as_closure().upvar_tys().iter().collect::<Vec<_>>(),
                        cl_args.as_closure().kind(),
                        *cl_def_id,
                    ),
                    other => panic!(
                        "illegal prusti::{}: expected closure, got {other:?}",
                        if builtin == PrustiBuiltin::Forall {
                            "forall"
                        } else {
                            "exists"
                        }
                    ),
                };

                let qvars = self.vcx.alloc_slice(
                    &qvar_tys
                        .iter()
                        .enumerate()
                        .map(|(idx, qvar_ty)| {
                            let ty_out = self.ty_use(qvar_ty);
                            self.vcx.mk_local_decl(
                                vir::vir_format!(self.vcx, "qvar_{}_{idx}", self.encoding_depth),
                                ty_out.snapshot,
                            )
                        })
                        .collect::<Vec<_>>(),
                );

                let mut reify_args = vec![];
                // TODO: big hack!
                //   the problem is that we expect this to
                //   be a simple Expr, but `encode_operand`
                //   returns an ExprRet; do we need ExprRet
                //   to be piped throughout this encoder?
                //   alternatively, can we have an "unlift"
                //   operation, which will work like reify
                //   but panicking on a Lazy(..)?
                let closure_ref = unsafe {
                    std::mem::transmute::<ExprRet<'_>, vir::ExprGen<'_, (), !, vir::Snap>>(
                        encoded_args[1],
                    )
                };
                // The signature of `forall` should enforce that the argument is
                // an `Fn` only.
                assert_eq!(cl_kind, ty::ClosureKind::Fn);

                reify_args.push(closure_ref);
                reify_args.extend(qvars.iter().map(|qvar| self.vcx.mk_local_ex(qvar)));

                // TODO: recursively invoke MirPure encoder to encode
                // the body of the closure; pass the closure as the
                // variable to use, then closure access = tuple access
                // (then hope to optimise this away later ...?)
                use vir::Reify;
                let body = self
                    .deps
                    .require_dep::<MirPureEnc>(MirPureEncTask {
                        encoding_depth: self.encoding_depth + 1,
                        kind: PureKind::Closure,
                        parent_def_id: cl_def_id,
                        param_env: self.vcx.tcx().param_env(cl_def_id),
                        substs: ty::List::identity_for_item(self.vcx.tcx(), cl_def_id),
                        caller_def_id: Some(self.def_id),
                    })
                    .unwrap()
                    .expr
                    // arguments to the closure are
                    // - the closure itself
                    // - the qvars
                    .reify(self.vcx, (cl_def_id, self.vcx.alloc_slice(&reify_args)))
                    .lift();

                let body =
                    bool.expect_native().snap_to_prim.call()(body.downcast_ty()).downcast_ty();
                // TODO: triggers
                let res = if builtin == PrustiBuiltin::Forall {
                    self.vcx.mk_forall_expr(qvars, &[], body)
                } else {
                    self.vcx.mk_exists_expr(qvars, &[], body)
                };
                mk_bool(res)
            }
            PrustiBuiltin::SliceLen => {
                assert_eq!(args.len(), 1);
                let op = self.encode_operand_snap(&args[0].node, curr_ver)?;
                let slice_ty = self
                    .vcx
                    .tcx()
                    .mk_ty_from_kind(TyKind::Slice(arg_tys[0].expect_ty()));
                let ref_slice_ty = self.vcx.tcx().mk_ty_from_kind(TyKind::Ref(
                    Region::new_var(self.vcx.tcx(), 0usize.into()),
                    slice_ty,
                    ty::Mutability::Not,
                ));
                let ref_ty_out = self.ty_use(ref_slice_ty).expect_immref();
                let slice_ty_out = self.ty_use(slice_ty).expect_array();
                let prim =
                    slice_ty_out.len(ref_ty_out.value_access(op.downcast_ty()).downcast_ty());
                let usize_ = self.ty_use(self.vcx.tcx().types.usize).expect_primitive();
                usize_.prim_to_snap.call()(prim.upcast_ty())
            }
            PrustiBuiltin::ModeStart(mode) => {
                match mode {
                    Mode::Old => {
                        assert!(!self.old_mode);
                        self.old_mode = true;
                    }
                    Mode::Rel(0) => {
                        assert!(!self.rel0_mode);
                        assert!(!self.rel1_mode);
                        self.rel0_mode = true;
                    }
                    Mode::Rel(_) => {
                        assert!(!self.rel1_mode);
                        assert!(!self.rel0_mode);
                        self.rel1_mode = true;
                    }
                    Mode::BeforeExpiry => {
                        assert!(!self.before_expiry_mode);
                        self.before_expiry_mode = true;
                    }
                }
                mk_bool(self.vcx.mk_bool::<true>().lift()) // TODO: what value do we return?
            }
            PrustiBuiltin::ModeEnd(mode) => {
                match mode {
                    Mode::Old => {
                        assert!(self.old_mode);
                        self.old_mode = false;
                    }
                    Mode::Rel(0) => {
                        assert!(self.rel0_mode);
                        assert!(!self.rel1_mode);
                        self.rel0_mode = false;
                    }
                    Mode::Rel(_) => {
                        assert!(!self.rel0_mode);
                        assert!(self.rel1_mode);
                        self.rel1_mode = false;
                    }
                    Mode::BeforeExpiry => {
                        assert!(self.before_expiry_mode);
                        self.before_expiry_mode = false;
                    }
                }
                mk_bool(self.vcx.mk_bool::<true>().lift()) // TODO: what value do we return?
            }
            PrustiBuiltin::IsNaN(fl) => {
                let is_nan_fun = match fl {
                    ty::FloatTy::F16 => {
                        self.ty_use(self.vcx.tcx().types.f16)
                            .expect_float()
                            .fp_is_nan
                    }
                    ty::FloatTy::F32 => {
                        self.ty_use(self.vcx.tcx().types.f32)
                            .expect_float()
                            .fp_is_nan
                    }
                    ty::FloatTy::F64 => {
                        self.ty_use(self.vcx.tcx().types.f64)
                            .expect_float()
                            .fp_is_nan
                    }
                    ty::FloatTy::F128 => {
                        self.ty_use(self.vcx.tcx().types.f128)
                            .expect_float()
                            .fp_is_nan
                    }
                };
                let fl = self.encode_operand_snap(&args[0].node, curr_ver)?;
                mk_bool(is_nan_fun.call()(fl.downcast_ty()))
            }
            PrustiBuiltin::IsInfinite(fl) => {
                let is_infinite_fun = match fl {
                    ty::FloatTy::F16 => {
                        self.ty_use(self.vcx.tcx().types.f16)
                            .expect_float()
                            .fp_is_infinite
                    }
                    ty::FloatTy::F32 => {
                        self.ty_use(self.vcx.tcx().types.f32)
                            .expect_float()
                            .fp_is_infinite
                    }
                    ty::FloatTy::F64 => {
                        self.ty_use(self.vcx.tcx().types.f64)
                            .expect_float()
                            .fp_is_infinite
                    }
                    ty::FloatTy::F128 => {
                        self.ty_use(self.vcx.tcx().types.f128)
                            .expect_float()
                            .fp_is_infinite
                    }
                };
                let fl = self.encode_operand_snap(&args[0].node, curr_ver)?;
                mk_bool(is_infinite_fun.call()(fl.downcast_ty()))
            }
            PrustiBuiltin::FlAbs(fl) => {
                let fl_ty = match fl {
                    ty::FloatTy::F16 => self.ty_use(self.vcx.tcx().types.f16),
                    ty::FloatTy::F32 => self.ty_use(self.vcx.tcx().types.f32),
                    ty::FloatTy::F64 => self.ty_use(self.vcx.tcx().types.f64),
                    ty::FloatTy::F128 => self.ty_use(self.vcx.tcx().types.f128),
                }
                .expect_float();
                let fl1 = self
                    .encode_operand_snap(&args[0].node, curr_ver)?
                    .downcast_ty();
                fl_ty.fp_abs.call()(fl1)
            }
            PrustiBuiltin::FlToReal => {
                let a_ty = args[0].node.ty(self.body, self.vcx.tcx());
                let fl_ty = self.ty_use(a_ty).expect_float();
                let fl = self
                    .encode_operand_snap(&args[0].node, curr_ver)?
                    .downcast_ty();
                let res = fl_ty.fp_to_real.call()(fl);
                self.ty_use_real().perm_to_snap.call()(res)
            }
            PrustiBuiltin::RealMul => self.encode_real_op(vir::BinOpKind::Mul, args, curr_ver)?,
            PrustiBuiltin::RealSub => self.encode_real_op(vir::BinOpKind::Sub, args, curr_ver)?,
            PrustiBuiltin::RealAdd => self.encode_real_op(vir::BinOpKind::Add, args, curr_ver)?,
            PrustiBuiltin::RealDiv => {
                self.encode_real_op(vir::BinOpKind::DivRationalRational, args, curr_ver)?
            }
            PrustiBuiltin::RealEq => self.encode_real_cmp(vir::BinOpKind::CmpEq, args, curr_ver)?,
            PrustiBuiltin::RealLt => self.encode_real_cmp(vir::BinOpKind::CmpLt, args, curr_ver)?,
            PrustiBuiltin::RealLe => self.encode_real_cmp(vir::BinOpKind::CmpLe, args, curr_ver)?,
            PrustiBuiltin::RealGt => self.encode_real_cmp(vir::BinOpKind::CmpGt, args, curr_ver)?,
            PrustiBuiltin::RealGe => self.encode_real_cmp(vir::BinOpKind::CmpGe, args, curr_ver)?,
            PrustiBuiltin::RealNeg => {
                let real = self.ty_use_real();
                let real_val = real.snap_to_perm.call()(
                    self.encode_operand_snap(&args[0].node, curr_ver)?
                        .downcast_ty(),
                );
                real.perm_to_snap.call()(
                    self.vcx
                        .mk_unary_op_expr(vir::UnOpKind::Neg, real_val.upcast_ty())
                        .downcast_ty(),
                )
            }
        }
        .upcast_ty())
    }
}

mod rev_doms {
    /// Identical to `body.basic_blocks.dominators()` except in reverse. Since
    /// there may be multiple `Return`/`Unreachable`/etc. terminators, we add a
    /// special end block index which is invalid in `basic_blocks` but pretends
    /// to be the successor of all these no-successor blocks.
    pub struct ReverseDominators {
        pub dom: dominators::Dominators<mir::BasicBlock>,
        pub end: mir::BasicBlock,
    }
    impl ReverseDominators {
        #[allow(clippy::needless_lifetimes)]
        pub fn new<'a, 'vir>(blocks: &'a mir::BasicBlocks<'vir>) -> Self {
            let no_succ_blocks = blocks
                .iter_enumerated()
                .filter(|(_, data)| {
                    /* The commented line below prevents e.g. a SwitchInt with a branch
                    going to an Unreachable terminator from having a join point, so
                    do not treat such terminators as return blocks. */
                    // data.terminator().successors().next().is_none()
                    matches!(
                        data.terminator().kind,
                        mir::TerminatorKind::Return | mir::TerminatorKind::UnwindResume
                    )
                })
                .map(|(bb, _)| bb)
                .collect();
            let rbb = RevBasicBlocks(blocks, no_succ_blocks);
            Self {
                dom: dominators::dominators(&rbb),
                end: rbb.start_node(),
            }
        }
        pub fn immediate_dominator(&self, bb: mir::BasicBlock) -> mir::BasicBlock {
            // This unwrap should never fail since all blocks can reach `end`
            self.dom.immediate_dominator(bb).unwrap()
        }
    }

    use super::*;
    use prusti_rustc_interface::data_structures::graph::*;

    /// A wrapper around `mir::BasicBlocks` which reverses the direction of the
    /// edges. Implements `ControlFlowGraph` such that we can call `dominators`.
    struct RevBasicBlocks<'a, 'vir>(&'a mir::BasicBlocks<'vir>, Vec<mir::BasicBlock>);
    impl DirectedGraph for RevBasicBlocks<'_, '_> {
        type Node = mir::BasicBlock;

        fn num_nodes(&self) -> usize {
            self.0.len() + 1
        }
    }
    impl StartNode for RevBasicBlocks<'_, '_> {
        fn start_node(&self) -> Self::Node {
            self.0.next_index()
        }
    }

    impl Predecessors for RevBasicBlocks<'_, '_> {
        fn predecessors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
            if node == self.start_node() {
                Box::new([].into_iter())
            } else if self.1.contains(&node) {
                Box::new([self.start_node()].into_iter())
            } else {
                Box::new(self.0.successors(node)) as Box<dyn Iterator<Item = _>>
            }
        }
    }

    impl Successors for RevBasicBlocks<'_, '_> {
        fn successors(&self, node: Self::Node) -> impl Iterator<Item = Self::Node> {
            if node == self.start_node() {
                Box::new(self.1.iter().copied()) as Box<dyn Iterator<Item = _>>
            } else {
                Box::new((&self.0).predecessors(node)) as Box<dyn Iterator<Item = _>>
            }
        }
    }
}

#[derive(Debug, Clone, Copy)]
struct Version<'vir> {
    index: usize,
    location: mir::Location,
    initialised: Option<vir::LocalDeclSnap<'vir>>,
}

impl<'vir> Default for Version<'vir> {
    fn default() -> Self {
        Self {
            index: 0,
            location: mir::Location::START,
            initialised: None,
        }
    }
}

impl<'vir> fmt::Display for Version<'vir> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        if cfg!(debug_assertions) {
            write!(
                f,
                "{:?}_s{}_i{}",
                self.location.block, self.location.statement_index, self.index
            )
        } else {
            write!(f, "{}", self.index)
        }
    }
}
