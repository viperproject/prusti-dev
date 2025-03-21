//#[macro_export]
//macro_rules! vir_expr_nopos {
//
//}

//#[macro_export]
//macro_rules! vir {
//    ($vcx: expr, $span: expr, $ops: tt) => {
//        $vcx.enter($span, |spanned_vcx| $ops)
//    };
//}

//#[macro_export]
//macro_rules! vir_span {
//    ($vcx: expr, $span: expr, $ops: tt) => {{
//        $vcx.span_stack.push($span);
//        let result = $ops;
//        $vcx.span_stack.pop();
//        result
//    }};
//}

//use crate::UnknownArity;

#[macro_export]
macro_rules! vir_type_list {
    ($vcx:expr; $( $args:tt ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut v = vec![];
        $( v.push($crate::vir_type!($vcx; $args)); )*
        $vcx.alloc_slice(&v)
    }};
}

#[macro_export]
macro_rules! vir_arg_list {
    ($vcx:expr; $( $name:tt : $ty:tt ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut v = vec![];
        $( v.push($crate::vir_local_decl!($vcx; $name : $ty)); )*
        $vcx.alloc_slice(&v)
    }};
}

/*
#[macro_export]
macro_rules! vir_expr_list {
    ($vcx:expr; $( $args:tt ),* $(,)? ) => {{
        let mut v = vec![];
        $( println!("expr list arg: {}", stringify!($args)); )*
        $( v.push($crate::vir_expr!($vcx; $args)); )*
        v
    }};
}

// TODO: $crate:: for vir as well?
#[macro_export]
macro_rules! vir_expr {
    ($vcx:expr; forall([ $( $args:tt )* ] $( $body:tt )*)) => {{
        &*$vcx.arena.alloc(ExprData::Forall(&*$vcx.arena.alloc(ForallData {
            qvars: bumpalo::vec![in &$vcx.arena],
            // triggers
            body: $crate::vir_expr!($vcx; $($body)*),
        })))
    }};
    ($vcx:expr; $target:ident ( $($args:tt),* )) => {{
        // TODO: arguments ...
        &*$vcx.arena.alloc(ExprData::FuncApp(&*$vcx.arena.alloc(FuncAppData {
            target: $vcx.alloc_str(stringify!($target)), // TODO: vir_ident
            args: $crate::vir_expr_list!($vcx; $($args)*),
            //args: bumpalo::vec![in &$vcx.arena; $( $crate::vir_expr!($vcx; $args) ),* ],
        })))
    }};
    ($vcx:expr; $name:ident) => {{
        &*$vcx.arena.alloc(ExprData::Local(&*$vcx.arena.alloc(LocalData {
            name: $vcx.alloc_str(stringify!($name)), // TODO: vir_ident
        })))
    }};
    ($vcx:expr; ($($lhs:tt)*) == ($($rhs:tt)*)) => {{
        &*$vcx.arena.alloc(ExprData::BinOp(&*$vcx.arena.alloc(BinOpData {
            kind: BinOpKind::CmpEq,
            lhs: $crate::vir_expr!($vcx; $($lhs)*),
            rhs: $crate::vir_expr!($vcx; $($rhs)*),
        })))
    }};
    ($vcx:expr; ($($e:tt)*)) => {{
        $crate::vir_expr!($vcx; $($e)*)
    }};

    /*
    ($vcx: expr, foo) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(ExprData::Foo)
    }};
    ($vcx: expr, ($lhs: tt) == ($rhs: tt)) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(ExprData::EqCmp($crate::vir_expr!($vcx, $lhs), $crate::vir_expr!($vcx, $rhs)))
    }};
    ($vcx: expr, !($sub: tt)) => {{
        assert!(!$vcx.span_stack.is_empty());
        &*$vcx.arena.alloc(ExprData::Neg($crate::vir_expr!($vcx, $sub)))
    }};*/
}
*/

#[macro_export]
macro_rules! vir_expr {
    ($vcx:expr; $( $args:tt )* ) => {
        &*$vcx.mk_todo_expr(
            $vcx.alloc_str(stringify!($($args)*)),
        )
    }
}

#[macro_export]
macro_rules! vir_ident {
    ($vcx:expr; [ $name:expr ]) => {
        $name
    };
    ($vcx:expr; $name:ident ) => {
        $vcx.alloc_str(stringify!($name))
    };
}

#[macro_export]
macro_rules! vir_format {
    ($vcx:expr, $($arg:tt)*) => { $vcx.alloc_str(&format!($($arg)*)) };
}

#[macro_export]
macro_rules! vir_format_identifier {
    ($vcx:expr, $($arg:tt)*) => { $crate::ViperIdent::sanitize($vcx, format!($($arg)*)) };
}

#[macro_export]
macro_rules! vir_type {
    ($vcx:expr; Bool) => {
        &$crate::TypeData::Bool
    };
    ($vcx:expr; Ref) => {
        &$crate::TypeData::Ref
    };
    ($vcx:expr; Uint($bit_width:expr)) => {
        $vcx.alloc($crate::TypeData::Int {
            signed: false,
            bit_width: $bit_width,
        })
    };
    ($vcx:expr; Int($bit_width:expr)) => {
        $vcx.alloc($crate::TypeData::Int {
            signed: true,
            bit_width: $bit_width,
        })
    };
    ($vcx:expr; [ $ty:expr ]) => {
        $ty
    };
    ($vcx:expr; $name:ident) => {
        $vcx.alloc($crate::TypeData::Domain(
            $vcx.alloc_str(stringify!($name)),
            &[],
        ))
    };
}

#[macro_export]
macro_rules! vir_local_decl {
    ($vcx:expr; $name:tt : $ty:tt) => {
        $vcx.alloc($crate::LocalDeclData {
            name: $crate::vir_ident!($vcx; $name),
            ty: $crate::vir_type!($vcx; $ty),
        })
    };
}

#[macro_export]
macro_rules! vir_domain_axiom {
    ($vcx:expr; axiom_inverse($a:tt, $b:tt, $ty:tt)) => {{
        let val_ex = $vcx.mk_local_ex("val", $crate::vir_type!($vcx; $ty));
        let inner = $b.apply($vcx, [val_ex]);
        $vcx.mk_domain_axiom(
            $vcx.alloc_str(&format!(
                "ax_inverse_{}_{}",
                $a.name(),
                $b.name(),
            )),
            $vcx.mk_forall_expr(
                $vcx.alloc_slice(&[
                    $vcx.mk_local_decl("val", $crate::vir_type!($vcx; $ty)),
                ]),
                $vcx.alloc_slice(&[$vcx.alloc_slice(&[inner])]),
                $vcx.mk_bin_op_expr(
                    $crate::BinOpKind::CmpEq,
                    $a.apply($vcx, [inner]),
                    val_ex,
                ),
            ),
        )
    }};
    ($vcx:expr; axiom $name:tt { $( $body:tt )* }) => {{
        $vcx.alloc($crate::DomainAxiomData {
            name: $crate::vir_ident!($vcx; $name),
            expr: $crate::vir_expr!($vcx; $($body)*),
        })
    }};
}

#[macro_export]
macro_rules! vir_domain_func {
    ($vcx:expr; unique function $name:tt ( $( $args:tt )* ): $ret:tt ) => {{
        $vcx.mk_domain_function(
            FunctionIdent::new(
                $name.name(),
                vir::UnknownArity::new($crate::vir_type_list!($vcx; $($args)*)),
                $crate::vir_type!($vcx; $ret),
            ),
            true
        )
    }};
    ($vcx:expr; function $name:tt ( $( $args:tt )* ): $ret:tt ) => {{
        $vcx.mk_domain_function(
            FunctionIdent::new(
                $name.name(),
                vir::UnknownArity::new($crate::vir_type_list!($vcx; $($args)*)),
                $crate::vir_type!($vcx; $ret),
            ),
            false
        )
    }};
}

#[macro_export]
macro_rules! vir_domain_members {
    ($vcx:expr; $axioms:expr; $functions:expr;
        axiom_inverse($a:tt, $b:tt, $ty:tt);
        $( $rest:tt )*
    ) => {{
        $axioms.push($crate::vir_domain_axiom!($vcx; axiom_inverse($a, $b, $ty)));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        unique function $name:tt ( $( $args:tt )* ): $ret:tt;
        $( $rest:tt )*
    ) => {{
        $functions.push($crate::vir_domain_func!($vcx; unique function $name( $($args)* ): $ret));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        function $name:tt ( $( $args:tt )* ): $ret:tt;
        $( $rest:tt )*
    ) => {{
        $functions.push($crate::vir_domain_func!($vcx; function $name( $($args)* ): $ret));
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        with_funcs [ $e:expr ];
        $( $rest:tt )*
    ) => {{
        $functions.extend($e);
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;
        with_axioms [ $e:expr ];
        $( $rest:tt )*
    ) => {{
        $axioms.extend($e);
        $crate::vir_domain_members!($vcx; $axioms; $functions; $($rest)*);
    }};
    ($vcx:expr; $axioms:expr; $functions:expr;) => {};
}

#[macro_export]
macro_rules! vir_domain {
    ($vcx:expr; domain $name:tt { $( $member:tt )* }) => {{
        #[allow(unused_mut)]
        let mut axioms = vec![];
        #[allow(unused_mut)]
        let mut functions = vec![];
        $crate::vir_domain_members!($vcx; axioms; functions; $($member)*);
        $vcx.mk_domain(
            $crate::ViperIdent::new($crate::vir_ident!($vcx; $name)),
            &[],
            $vcx.alloc_slice(&axioms),
            $vcx.alloc_slice(&functions),
        )
    }};
}

#[macro_export]
macro_rules! vir_predicate {
    ($vcx:expr; predicate $name:tt ( $( $args:tt )* ) { [$expr:expr] }) => {{
        $vcx.mk_predicate_unchecked(
            $crate::vir_ident!($vcx; $name),
            $crate::vir_arg_list!($vcx; $($args)*),
            Some($expr)
        )
    }};
    ($vcx:expr; predicate $name:tt ( $( $args:tt )* )) => {{
        $vcx.mk_predicate_unchecked(
            $crate::vir_ident!($vcx; $name),
            $crate::vir_arg_list!($vcx; $($args)*),
            None
        )
    }};
}

pub trait ExprApply<'vir, A> {
    fn expr_apply(&self, vcx: &'vir crate::VirCtxt<'vir>, args: &[A]) -> crate::Expr<'vir>;
}

impl<'vir> ExprApply<'vir, crate::Expr<'vir>> for crate::FunctionIdent<'vir, crate::UnknownArity<'vir>> {
    fn expr_apply(&self, vcx: &'vir crate::VirCtxt<'vir>, args: &[crate::Expr<'vir>]) -> crate::Expr<'vir> {
        self.apply(vcx, args)
    }
}
impl<'vir, const N: usize> ExprApply<'vir, crate::Expr<'vir>> for crate::FunctionIdent<'vir, crate::KnownArity<'vir, N>> {
    fn expr_apply(&self, vcx: &'vir crate::VirCtxt<'vir>, args: &[crate::Expr<'vir>]) -> crate::Expr<'vir> {
        assert_eq!(args.len(), N);
        self.apply(vcx, args.try_into().unwrap())
    }
}
impl<'vir> ExprApply<'vir, crate::Expr<'vir>> for crate::PredicateIdent<'vir, crate::UnknownArity<'vir>> {
    fn expr_apply(&self, vcx: &'vir crate::VirCtxt<'vir>, args: &[crate::Expr<'vir>]) -> crate::Expr<'vir> {
        vcx.mk_predicate_app_expr(self.apply(vcx, args, None))
    }
}
impl<'vir> ExprApply<'vir, crate::Expr<'vir>> for crate::Field<'vir> {
    fn expr_apply(&self, vcx: &'vir crate::VirCtxt<'vir>, args: &[crate::Expr<'vir>]) -> crate::Expr<'vir> {
        assert_eq!(args.len(), 1);
        vcx.mk_field_expr(args[0], self)
    }
}

pub trait ExprQuote<'vir> {
    fn expr(&self, vcx: &'vir crate::VirCtxt<'vir>) -> crate::Expr<'vir>;
}

impl<'vir> ExprQuote<'vir> for crate::Expr<'vir> {
    fn expr(&self, _vcx: &'vir crate::VirCtxt<'vir>) -> crate::Expr<'vir> {
        self
    }
}
impl<'vir> ExprQuote<'vir> for crate::Local<'vir> {
    fn expr(&self, vcx: &'vir crate::VirCtxt<'vir>) -> crate::Expr<'vir> {
        vcx.mk_local_ex_local(self)
    }
}

#[macro_export]
macro_rules! expr {
    (@typ; [$outer:expr]) => { $outer };
    (@typ; Bool) => { &$crate::TypeData::Bool };
    (@typ; Int) => { &$crate::TypeData::Int };
    (@typ; Ref) => { &$crate::TypeData::Ref };

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
    (@forall_qvars($output:ident, $qvars:ident); ..[$outer:expr] $($tokens:tt)*) => { {
        $qvars.extend($outer.iter().map(|local| vcx!().mk_local_decl_local(local)));
        $crate::expr!(@forall_qvars($output, $qvars); $($tokens)*)
    } };
    (@forall_qvars($output:ident, $qvars:ident); $qvar:ident : $qtype:tt $($tokens:tt)* ) => { {
        let local = vcx!().mk_local(stringify!($qvar), $crate::expr!(@typ; $qtype));
        $qvars.push(vcx!().mk_local_decl_local(local));
        let $qvar: $crate::Expr = vcx!().mk_local_ex_local(local);
        $crate::expr!(@forall_qvars($output, $qvars); $($tokens)*)
    } };
    (@forall_qvars($output:ident, $qvars:ident); , $($tokens:tt)* ) => { // TODO: this accepts too many commas
        $crate::expr!(@forall_qvars($output, $qvars); $($tokens)*)
    };
    (@forall_qvars($output:ident, $qvars:ident); ) => { compile_error!("malformed forall") };

    (@expr_done($output:ident); , $($tokens:tt)+) => { $crate::expr!(@expr($output); $($tokens)*) };
    (@expr_done($output:ident); $($tokens:tt)+) => { compile_error!("unexpected VIR expression (missing comma?)") };
    (@expr_done($output:ident);) => {};

    (@expr($output:ident); unfolding_wildcard ( [ $outer:expr ]( $($args:tt)* ) ) in ( $($rhs:tt)+ ) ) => { { $output.push(vcx!().mk_unfolding_expr(
        $outer.apply(vcx!(),
            $crate::expr!(@expr_list; $($args)*).as_slice(),
            Some(vcx!().mk_wildcard()),
        ),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); acc( [ $outer:expr ]( $($args:tt)* ) ) ) => { { $output.push(vcx!().mk_predicate_app_expr(
        $outer.apply(vcx!(),
            $crate::expr!(@expr_list; $($args)*).as_slice(),
            None,
        )
    )); } };
    (@expr($output:ident); acc_field( [ $outer:expr ]( $($args:tt)* ) ) ) => { { $output.push(vcx!().mk_acc_field_expr(
        $crate::expr!(@expr_one; $($args)*),
        $outer,
        None,
    )); } };
    (@expr($output:ident); acc_wildcard( [ $outer:expr ]( $($args:tt)* ) ) ) => { { $output.push(vcx!().mk_predicate_app_expr(
        $outer.apply(vcx!(),
            $crate::expr!(@expr_list; $($args)*).as_slice(),
            Some(vcx!().mk_wildcard()),
        )
    )); } };
    (@expr($output:ident); [ $outer:expr ]( ) ) => { { $output.push($outer.expr_apply(
        vcx!(),
        &[],
    )); } };
    (@expr($output:ident); [ $outer:expr ]( $($args:tt)* ) ) => { { $output.push($outer.expr_apply(
        vcx!(),
        $crate::expr!(@expr_list; $($args)*).as_slice(),
    )); } };
    (@expr($output:ident); [ $outer:expr ] ) => { { $output.push($outer.expr(vcx!())); } };
    (@expr($output:ident); ..[ $outer:expr ] ) => { { $output.extend($outer.iter().map(|e| e.expr(vcx!()))); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) => ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::Implies,
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) == ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_eq_expr(
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) && ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_conj(&[
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    ])); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) <= ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::CmpLe,
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) < ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::CmpLt,
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); ( $($lhs:tt)+ ) + ( $($rhs:tt)+ )) => { { $output.push(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::Add,
        $crate::expr!(@expr_one; $($lhs)*),
        $crate::expr!(@expr_one; $($rhs)*),
    )); } };
    (@expr($output:ident); null) => { { $output.push(vcx!().mk_null()); } };
    (@expr($output:ident); true) => { { $output.push(vcx!().mk_bool::<true>()); } };
    (@expr($output:ident); false) => { { $output.push(vcx!().mk_bool::<false>()); } };
    (@expr($output:ident); result) => { { $output.push(vcx!().mk_result()); } };
    (@expr($output:ident); forall $($tokens:tt)+) => { {
        let mut qvars = Vec::new();
        $crate::expr!(@forall_qvars($output, qvars); $($tokens)*)
    } };
    (@expr($output:ident); $ident:ident $($rest:tt)*) => { { $output.push($ident.expr(vcx!())); $crate::expr!(@expr_done($output); $($rest)*); } };
    (@expr($output:ident); $($tokens:tt)+) => { compile_error!("VIR syntax error") };
    (@expr($output:ident);) => { compile_error!("unexpected end of VIR expression") };

    (@expr_one; $($tokens:tt)*) => { {
        #[allow(unused_mut)]
        let mut output: Vec<$crate::Expr> = Vec::with_capacity(1);
        $crate::expr!(@expr(output); $($tokens)*);
        assert_eq!(output.len(), 1, "expected one VIR expression");
        output[0]
    } };
    (@expr_list;) => { Vec::new() };
    (@expr_list; $($tokens:tt)*) => { {
        #[allow(unused_mut)]
        let mut output: Vec<$crate::Expr> = Vec::new();
        $crate::expr!(@expr(output); $($tokens)*);
        output
    } };

    ($vcx:expr; $($tokens:tt)+) => { {
        use $crate::macros::{ExprApply, ExprQuote};
        let vcx = $vcx; macro_rules! vcx { () => { vcx }; }
        $crate::expr!(@expr_one; $($tokens)*)
    } };
    ($($tokens:tt)+) => { vir::with_vcx(|vcx| {
        use $crate::macros::{ExprApply, ExprQuote};
        #[allow(unused)]
        macro_rules! vcx { () => { vcx }; }
        $crate::expr!(@expr_one; $($tokens)*)
    }) };
    () => { compile_error!("expected VIR expression") };
}
