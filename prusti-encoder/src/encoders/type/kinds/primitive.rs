use prusti_rustc_interface::middle::ty;
use task_encoder::{EncodeFullError, TaskEncoder, TaskEncoderDependencies, TaskEncoderError};
use vir::{Arity, FunctionIdent, ToKnownArity, UnknownArity};

use crate::encoders::{domain::{DomainBuilder, DomainDataPrim, DomainEnc, DomainEncSpecifics}, most_generic_ty::get_vir_base_name_kind};

trait ExprApply<'vir, A> {
    fn expr_apply(&self, vcx: &'vir vir::VirCtxt<'vir>, args: &[A]) -> vir::Expr<'vir>;
}
trait ExprQuote<'vir> {
    fn expr(&self, vcx: &'vir vir::VirCtxt<'vir>) -> vir::Expr<'vir>;
}

impl<'vir> ExprApply<'vir, vir::Expr<'vir>> for FunctionIdent<'vir, UnknownArity<'vir>> {
    fn expr_apply(&self, vcx: &'vir vir::VirCtxt<'vir>, args: &[vir::Expr<'vir>]) -> vir::Expr<'vir> {
        self.apply(vcx, args)
    }
}
impl<'vir> ExprQuote<'vir> for vir::Expr<'vir> {
    fn expr(&self, _vcx: &'vir vir::VirCtxt<'vir>) -> vir::Expr<'vir> {
        self
    }
}

#[macro_export]
macro_rules! expr {
    (@typ; [$outer:expr]) => { $outer };
    (@typ; Bool) => { &vir::TypeData::Bool };
    (@typ; Int) => { &vir::TypeData::Int };
    (@typ; Ref) => { &vir::TypeData::Ref };

    (@forall_qvars($output:ident, $qvars:ident); :: { $($triggers:tt)* } $($tokens:tt)*) => { $output.push(vcx!().mk_forall_expr(
        vcx!().alloc_slice($qvars.as_slice()),
        vcx!().alloc_slice($crate::expr!(@expr_list; $($triggers)*).into_iter().map(|e| vcx!().mk_trigger(&[e])).collect::<Vec<_>>().as_slice()),
        $crate::expr!(@expr_one; $($tokens)*),
    )) };
    (@forall_qvars($output:ident, $qvars:ident); :: $($tokens:tt)*) => { $output.push(vcx!().mk_forall_expr(
        // TODO: warn: no triggers provided?
        vcx!().alloc_slice($qvars.as_slice()),
        &[],
        $crate::expr!(@expr_one; $($tokens)*),
    )) };
    (@forall_qvars($output:ident, $qvars:ident); $qvar:ident : $qtype:tt $($tokens:tt)*) => { {
        let local = vcx!().mk_local(stringify!($qvar), $crate::expr!(@typ; $qtype)); // TODO: parse type
        $qvars.push(vcx!().mk_local_decl_local(local));
        let $qvar = vcx!().mk_local_ex_local(local);
        $crate::expr!(@forall_qvars($output, $qvars); $($tokens)*)
    } };
    (@forall_qvars($output:ident, $qvars:ident); ) => { compile_error!("malformed forall") };

    (@expr($output:ident); [ $outer:expr ]( $($args:tt)* ) ) => { { $output.push($outer.expr_apply(
        vcx!(),
        $crate::expr!(@expr_list; $($args)*).as_slice(),
    )); } };
    (@expr($output:ident); [ $outer:expr ] ) => { { $output.push($outer.expr(vcx!())); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) == ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_eq_expr(
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) && ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_conj(&[
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    ])); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) <= ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_bin_op_expr(
        vir::BinOpKind::CmpLe,
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); null) => { { $output.push(vcx!().mk_null()); } };
    (@expr($output:ident); true) => { { $output.push(vcx!().mk_bool::<true>()); } };
    (@expr($output:ident); false) => { { $output.push(vcx!().mk_bool::<false>()); } };
    (@expr($output:ident); forall $($tokens:tt)+) => { {
        let mut qvars = Vec::new();
        $crate::expr!(@forall_qvars($output, qvars); $($tokens)*)
    } };
    (@expr($output:ident); $ident:ident) => { { $output.push($ident); } };
    (@expr($output:ident); $($tokens:tt)+) => { compile_error!("syntax error") };
    (@expr($output:ident);) => { compile_error!("unexpected end of VIR expression") };

    (@expr_one; $($tokens:tt)*) => { {
        #[allow(unused_mut)]
        let mut output: Vec<vir::Expr> = Vec::with_capacity(1);
        $crate::expr!(@expr(output); $($tokens)*);
        assert_eq!(output.len(), 1, "expected one VIR expression");
        output[0]
    } };
    (@expr_list; $($tokens:tt)*) => { {
        #[allow(unused_mut)]
        let mut output: Vec<vir::Expr> = Vec::new();
        $crate::expr!(@expr(output); $($tokens)*);
        output
    } };

    ($vcx:expr; $($tokens:tt)+) => { {
        let vcx = $vcx; macro_rules! vcx { () => { vcx }; }
        $crate::expr!(@expr_one; $($tokens)*)
    } };
    ($($tokens:tt)+) => { vir::with_vcx(|vcx| {
        macro_rules! vcx { () => { vcx }; }
        $crate::expr!(@expr_one; $($tokens)*)
    }) };
    () => { compile_error!("expected VIR expression") };
}

pub(crate) fn domain<'vir>(
    task_key: <DomainEnc as TaskEncoder>::TaskKey<'vir>,
    deps: &mut TaskEncoderDependencies<'vir, DomainEnc>,
    builder: &mut DomainBuilder<'vir>,
) -> Result<DomainEncSpecifics<'vir>, EncodeFullError<'vir, DomainEnc>> {
    let ty = task_key.ty();
    let ty_kind = ty.kind();
    let prim_type = match ty_kind {
        ty::TyKind::Bool => &vir::TypeData::Bool,
        ty::TyKind::Char
        | ty::TyKind::Int(_)
        | ty::TyKind::Uint(_) => &vir::TypeData::Int,
        ty::TyKind::Float(_) => todo!(),
        _ => unreachable!(),
    };

    let base_name = get_vir_base_name_kind(&ty_kind, builder.vcx);
    builder.set_name(&base_name);

    let typeof_ident = builder.function("typeof", &[builder.self_type()], builder.type_type());

    deps.emit_output_ref(task_key, builder.output_ref(base_name, typeof_ident.to_known()))?;

    let value_ident = builder.function("value", &[builder.self_type()], prim_type);
    let cons_ident = builder.function("cons", &[prim_type], builder.self_type());

    builder.axiom("value", expr! {
        forall value: [prim_type] :: {[cons_ident](value)} ([value_ident]([cons_ident](value))) == (value)
    });
    builder.axiom("cons", expr! {
        forall s: [builder.self_type()] :: {[value_ident](s)} ([cons_ident]([value_ident](s))) == (s)
    });

    match ty_kind {
        ty::TyKind::Int(_) => {
            let min = builder.vcx.get_min_int(&ty_kind);
            let max = builder.vcx.get_max_int(&ty_kind);
            builder.axiom("bounds", expr! {
                forall s: [builder.self_type()] :: {[value_ident](s)} (([min]) <= ([value_ident](s))) && (([value_ident](s)) <= ([max]))
            });
        }
        _ => (),
    }

    Ok(DomainEncSpecifics::Primitive(DomainDataPrim {
        prim_type,
        snap_to_prim: value_ident.to_known(),
        prim_to_snap: cons_ident.to_known(),
    }))

    /*

    let prim_type_args = vec![FieldTy {
        ty: prim_type,
        rust_ty_data: None,
    }];
    let data = self.mk_field_functions(&prim_type_args, None, ty.is_integral());
    // TODO: what to do about write?
    let snap_to_prim = data.field_access[0].read;
    let specifics = DomainDataPrim {
        prim_type,
        snap_to_prim,
        prim_to_snap: data.field_snaps_to_snap.to_known(),
    };
    if let Some((lower, upper)) = specifics.bounds(ty) {
        let exp = snap_to_prim.apply(self.vcx, [self.self_ex]);
        let axiom = self.mk_bounds_axiom(self.domain.name_str(), exp, lower, upper);
        self.axioms.push(axiom);
    }
    DomainEncSpecifics::Primitive(specifics)
    */
}

/*


domain s_Int_i32 {
  axiom ax_s_Int_i32_cons_read_0 {
    forall f0: Int :: {s_Int_i32_cons(f0)} (s_Int_i32_read_0(s_Int_i32_cons(f0))) == (f0)
  }
  axiom ax_s_Int_i32_cons {
    forall self: s_Int_i32 :: {s_Int_i32_read_0(self)} (s_Int_i32_cons(s_Int_i32_read_0(self))) == (self)
  }
  axiom ax_s_Int_i32_write_0_read_0 {
    forall self: s_Int_i32, val: Int :: {s_Int_i32_read_0(s_Int_i32_write_0(self, val))} (s_Int_i32_read_0(s_Int_i32_write_0(self, val))) == (val)
  }
  axiom s_Int_i32_bounds {
    forall self: s_Int_i32 :: {s_Int_i32_read_0(self)} ((-(2147483648)) <= (s_Int_i32_read_0(self))) && ((s_Int_i32_read_0(self)) <= (2147483647))
  }
  function typeof_s_Int_i32(s_Int_i32): Type
  function s_Int_i32_cons(Int): s_Int_i32
  function s_Int_i32_read_0(s_Int_i32): Int
  function s_Int_i32_write_0(s_Int_i32, Int): s_Int_i32
}
*/
