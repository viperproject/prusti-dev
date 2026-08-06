use task_encoder::TaskEncoder;
use vir::CastType;

use crate::encoders::{
    Pure,
    ty::{
        RustTy, RustTyDecomposition,
        generics::{GenericParamsEnc, casters::CastersEnc},
        interior_mut::{ImTys, TyInteriorMutEnc},
    },
};

pub(in crate::encoders::ty) struct InteriorMutGenericsEnc;

impl TaskEncoder for InteriorMutGenericsEnc {
    task_encoder::encoder_cache!(InteriorMutGenericsEnc);
    const ENCODER_NAME: &'static str = "interior mutability generics encoder";
    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputFullLocal<'vir> = Vec<vir::DomainAxiom<'vir>>;

    fn task_to_key<'vir>(task: &Self::TaskDescription<'vir>) -> Self::TaskKey<'vir> {
        *task
    }

    fn do_encode_full<'vir>(
        task_key: &Self::TaskKey<'vir>,
        deps: &mut task_encoder::TaskEncoderDependencies<'vir, Self>,
    ) -> task_encoder::EncodeFullResult<'vir, Self> {
        deps.emit_output_ref(*task_key, ())?;
        let (param, concrete) = task_key;
        assert!(param.specifics.is_param() && !concrete.specifics.is_param());

        let casters = deps.require_ref::<CastersEnc<Pure>>(*task_key)?;
        let im_param = deps.require_ref::<TyInteriorMutEnc>(param)?;
        let im_concrete = deps.require_ref::<TyInteriorMutEnc>(concrete)?;

        // For each of the two `_IM_N` functions:
        // forall r: Ref, s: s_Param, [m: Map,] tys: ManyTyVal, cs: ManyCSnap ::
        //   { s_Param_IM_N(r, s, [m,] MyType_cons(tys, cs), []) }
        //   s_Param_IM_N(r, s, [m,] MyType_cons(tys, cs), []) ==
        //   s_MyType_IM_N(r, make_concrete(s, tys, cs), [m,] tys, cs)

        let params = deps.require_dep::<GenericParamsEnc>(concrete.params)?;
        let ty_expr = params.ty_expr(deps, RustTyDecomposition::identity(concrete))?;
        let tys = ImTys::new(deps);

        let axioms = vir::with_vcx(|vcx| {
            let common_qvars = |extra: &[vir::LocalDeclDyn<'vir>]| {
                let tys = params.ty_decls().iter().copied().map(vir::LocalDeclData::as_dyn);
                let cs = params.const_decls().iter().copied().map(vir::LocalDeclData::as_dyn);
                extra
                    .iter()
                    .copied()
                    .chain(tys)
                    .chain(cs)
                    .collect::<Vec<_>>()
            };
            let make_concrete = |s_exp: vir::ExprPSnap<'vir>| {
                casters.make_concrete.call()(s_exp, params.ty_exprs(), params.const_exprs())
                    .upcast_ty()
            };

            // Level 0: s_Param_IM_0(r, s, MyType) == s_Ty_IM_0(r, make_concrete(s), ..)
            let l0_axiom = {
                let r = vcx.mk_local_decl("r", vir::TYPE_REF);
                let s = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
                let r_exp = vcx.mk_local_ex(r);
                let s_exp = vcx.mk_local_ex(s);
                let lhs = im_param.l0.call()(r_exp, s_exp.upcast_ty(), &[ty_expr], &[]);
                let rhs = im_concrete.l0.call()(
                    r_exp,
                    make_concrete(s_exp),
                    params.ty_exprs(),
                    params.const_exprs(),
                );
                let body = vcx.mk_eq_expr(lhs, rhs);
                let qvars = common_qvars(&[r.as_dyn(), s.as_dyn()]);
                let forall = vcx.mk_forall_expr(
                    vcx.alloc_slice(&qvars),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[lhs])]),
                    body,
                );
                let name = vir::ViperIdent::new(vir::vir_format!(
                    vcx,
                    "ax_{}_Param_IM_0",
                    concrete.name()
                ));
                vcx.mk_domain_axiom(name, forall)
            };

            // Level 1: takes the extra level-0 `Map` snapshot argument `m`.
            // s_Param_IM_1(r, s, m, MyType) == s_Ty_IM_1(r, make_concrete(s), m, ..)
            let l1_axiom = {
                let r = vcx.mk_local_decl("r", vir::TYPE_REF);
                let s = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
                let m = vcx.mk_local_decl("m", tys.snap_map);
                let r_exp = vcx.mk_local_ex(r);
                let s_exp = vcx.mk_local_ex(s);
                let m_exp = vcx.mk_local_ex(m);
                let lhs = im_param.l1.call()(r_exp, s_exp.upcast_ty(), m_exp, &[ty_expr], &[]);
                let rhs = im_concrete.l1.call()(
                    r_exp,
                    make_concrete(s_exp),
                    m_exp,
                    params.ty_exprs(),
                    params.const_exprs(),
                );
                let body = vcx.mk_eq_expr(lhs, rhs);
                let qvars = common_qvars(&[r.as_dyn(), s.as_dyn(), m.as_dyn()]);
                let forall = vcx.mk_forall_expr(
                    vcx.alloc_slice(&qvars),
                    vcx.alloc_slice(&[vcx.mk_trigger(&[lhs])]),
                    body,
                );
                let name = vir::ViperIdent::new(vir::vir_format!(
                    vcx,
                    "ax_{}_Param_IM_1",
                    concrete.name()
                ));
                vcx.mk_domain_axiom(name, forall)
            };

            vec![l0_axiom, l1_axiom]
        });
        Ok((axioms, ()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let axioms = Self::all_outputs_local_no_errors(program)
            .into_iter()
            .flatten()
            .collect::<Vec<_>>();
        let domain = vir::with_vcx(|vcx| {
            let name = vir::ViperIdent::new("def_Param_IM");
            let axioms = vcx.alloc_slice(&axioms);
            vcx.mk_domain(name, &[], axioms, &[], None)
        });
        program.add_domain(domain);
    }
}
