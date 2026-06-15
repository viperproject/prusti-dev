use task_encoder::TaskEncoder;
use vir::CastType;

use crate::encoders::{
    Pure,
    ty::{
        RustTy, RustTyDecomposition,
        generics::{GenericParamsEnc, casters::CastersEnc},
        interior_mut::TyInteriorMutEnc,
    },
};

pub(in crate::encoders::ty) struct InteriorMutGenericsEnc;

impl TaskEncoder for InteriorMutGenericsEnc {
    task_encoder::encoder_cache!(InteriorMutGenericsEnc);
    const ENCODER_NAME: &'static str = "interior mutability generics encoder";
    type TaskDescription<'vir> = (RustTy<'vir>, RustTy<'vir>);
    type OutputFullLocal<'vir> = vir::DomainAxiom<'vir>;

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

        // forall r: Ref, s: s_Param, tys: ManyTyVal, cs: ManyCSnap :: { s_Param_IM(r, s, MyType_cons(tys, cs), []) } s_Param_IM(r, s, MyType_cons(tys, cs), []) == s_MyType_IM(r, make_concrete(s, tys, cs), tys, cs)

        let params = deps.require_dep::<GenericParamsEnc>(concrete.params)?;
        let ty_expr = params.ty_expr(deps, RustTyDecomposition::identity(concrete))?;

        let axiom = vir::with_vcx(|vcx| {
            let r = vcx.mk_local_decl("r", vir::TYPE_REF);
            let s = vcx.mk_local_decl("s", vir::TYPE_PSNAP);
            let tys = params.ty_decls();
            let cs = params.const_decls();

            let r_exp = vcx.mk_local_ex(r);
            let s_exp = vcx.mk_local_ex(s);

            let lhs = im_param.0.call()(r_exp, s_exp.upcast_ty(), &[ty_expr], &[]);
            let rhs = im_concrete.0.call()(
                r_exp,
                casters.make_concrete.call()(s_exp, params.ty_exprs(), params.const_exprs())
                    .upcast_ty(),
                params.ty_exprs(),
                params.const_exprs(),
            );
            let body = vcx.mk_eq_expr(lhs, rhs);

            let tys = tys.iter().copied().map(vir::LocalDeclData::as_dyn);
            let cs = cs.iter().copied().map(vir::LocalDeclData::as_dyn);
            let qvars = [r.as_dyn(), s.as_dyn()]
                .into_iter()
                .chain(tys)
                .chain(cs)
                .collect::<Vec<_>>();
            let qvars = vcx.alloc_slice(&qvars);
            let triggers = vcx.alloc_slice(&[vcx.mk_trigger(&[lhs])]);
            let forall = vcx.mk_forall_expr(qvars, triggers, body);
            let name =
                vir::ViperIdent::new(vir::vir_format!(vcx, "ax_{}_Param_IM", concrete.name()));
            vcx.mk_domain_axiom(name, forall)
        });
        Ok((axiom, ()))
    }

    fn emit_outputs<'vir>(program: &mut task_encoder::Program<'vir>) {
        let axioms = Self::all_outputs_local_no_errors(program);
        let domain = vir::with_vcx(|vcx| {
            let name = vir::ViperIdent::new("def_Param_IM");
            let axioms = vcx.alloc_slice(&axioms);
            vcx.mk_domain(name, &[], axioms, &[], None)
        });
        program.add_domain(domain);
    }
}
