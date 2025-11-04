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

use crate::CompType;

#[macro_export]
macro_rules! vir_type_list {
    ($vcx:expr; $arg:tt $(,)? ) => {
        $crate::vir_type!($vcx; $arg)
    };
    ($vcx:expr; $( $args:tt ),* $(,)? ) => {
        ($($crate::vir_type!($vcx; $args)),*)
    };
}

#[macro_export]
macro_rules! vir_arg_list {
    ($vcx:expr; $( $name:tt : $ty:tt ),* $(,)? ) => {{
        #[allow(unused_mut)]
        let mut v = vec![];
        $( v.push($crate::CastType::as_dyn($crate::vir_local_decl!($vcx; $name : $ty))); )*
        $vcx.alloc_slice(&v)
    }};
}

#[macro_export]
macro_rules! vir_arg_tuple {
    ($vcx:expr; $( $name:tt : $ty:tt ),* $(,)? ) => {
        ($( $crate::vir_local_decl!($vcx; $name : $ty), )*)
    };
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
    ($vcx:expr, $($arg:tt)*) => { $crate::ViperIdent::sanitize($vcx, &format!($($arg)*)) };
}

#[macro_export]
macro_rules! vir_type {
    ($vcx:expr; Bool) => {
        $crate::TYPE_BOOL
    };
    ($vcx:expr; Ref) => {
        $crate::TYPE_REF
    };
    ($vcx:expr; Int) => {
        $crate::TYPE_INT
    };
    ($vcx:expr; Perm) => {
        $crate::TYPE_PERM
    };
    ($vcx:expr; Type) => {
        $crate::TYPE_TYVAL
    };
    ($vcx:expr; [ $ty:expr ]) => {
        $ty
    };
    ($vcx:expr; $name:ident) => {
        $vcx.alloc($crate::TypeData::<$crate::Dyn>::new(
            $crate::TypeKind::Domain($vcx.alloc_str(stringify!($name)), &[]),
        ))
    };
}

#[macro_export]
macro_rules! vir_local_decl {
    ($vcx:expr; $name:tt : $ty:tt) => {
        $vcx.mk_local_decl($crate::vir_ident!($vcx; $name), $crate::vir_type!($vcx; $ty))
    };
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

pub trait ExprApply<'vir, A: core::marker::Tuple, Ty: CompType> {
    fn expr_apply(self, vcx: &'vir crate::VirCtxt, args: A) -> crate::Expr<'vir, Ty>;
}

impl<'a, 'vir, A: crate::Arity, R: CompType> ExprApply<'vir, A::Exprs<'a, 'vir, (), !>, R>
    for crate::FunctionIdn<'vir, A, R>
{
    fn expr_apply(
        self,
        _vcx: &'vir crate::VirCtxt,
        args: A::Exprs<'a, 'vir, (), !>,
    ) -> crate::Expr<'vir, R> {
        self.call_once(args)
    }
}
impl<'a, 'vir, A: crate::Arity> ExprApply<'vir, A::Exprs<'a, 'vir, (), !>, crate::Bool>
    for crate::PredicateIdn<'vir, A>
{
    fn expr_apply(
        self,
        vcx: &'vir crate::VirCtxt,
        args: A::Exprs<'a, 'vir, (), !>,
    ) -> crate::ExprBool<'vir> {
        vcx.mk_predicate_app_expr(self.call_once(args)(None))
    }
}
impl<'vir, Ty: CompType> ExprApply<'vir, (crate::ExprRef<'vir>,), Ty> for crate::Field<'vir, Ty> {
    fn expr_apply(
        self,
        _vcx: &'vir crate::VirCtxt,
        args: (crate::ExprRef<'vir>,),
    ) -> crate::Expr<'vir, Ty> {
        self.call_once(args)
    }
}
impl<'vir, I: CompType, Ty: CompType> ExprApply<'vir, (crate::Expr<'vir, I>,), Ty>
    for crate::AdtDestructor<'vir, I, Ty>
{
    fn expr_apply(
        self,
        _vcx: &'vir crate::VirCtxt,
        args: (crate::Expr<'vir, I>,),
    ) -> crate::Expr<'vir, Ty> {
        self.call().call_once(args)
    }
}

pub trait ExprQuote<'vir, Ty: CompType> {
    fn expr(&self, vcx: &'vir crate::VirCtxt) -> crate::Expr<'vir, Ty>;
}

impl<'vir, Ty: CompType> ExprQuote<'vir, Ty> for crate::Expr<'vir, Ty> {
    fn expr(&self, _vcx: &'vir crate::VirCtxt) -> crate::Expr<'vir, Ty> {
        self
    }
}
impl<'vir, Ty: CompType> ExprQuote<'vir, Ty> for crate::LocalDecl<'vir, Ty> {
    fn expr(&self, vcx: &'vir crate::VirCtxt) -> crate::Expr<'vir, Ty> {
        vcx.mk_local_ex(self)
    }
}

#[macro_export]
macro_rules! expr {
    ($vcx:tt; $($tokens:tt)*) => { {
        use $crate::macros::{ExprApply, ExprQuote};
        let vcx = $vcx; #[allow(unused)] macro_rules! vcx { () => { vcx }; }
        $crate::expr_inner!(@expr_one; $($tokens)*)
    } };
    ($($tokens:tt)+) => { vir::with_vcx(|vcx| $crate::expr!(vcx; $($tokens)*)) };
    () => { compile_error!(concat!("VIR malformed empty")) };
}

#[macro_export]
macro_rules! expr_inner {
    (@expr_one; ($($e:tt)+) as $ty:ident) => {
        $crate::CastType::inner_cast_ty::<$crate::$ty>($crate::expr_inner!(@expr_one; $($e)*))
    };
    (@expr_one; unfolding ( [ $outer:expr ] ( $($args:tt)* ) ) in ( $($rhs:tt)+ ) ) => { vcx!().mk_unfolding_expr(
        $outer.call_once($crate::expr_inner!(@expr_args; $($args)*))(None),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ) };
    (@expr_one; acc( [ $outer:expr ] ( $($args:tt)* ) ) ) => { {
        let pred: $crate::PredicateIdn<_> = $outer;
        pred.expr_apply(
            vcx!(),
            $crate::expr_inner!(@expr_args; $($args)*),
        )
    } };
    (@expr_one; acc( ( $($args:tt)+ ).[ $outer:expr ] ) ) => { vcx!().mk_acc_field_expr(
        $crate::expr_inner!(@expr_one; $($args)*),
        $outer,
        None,
    ) };
    (@expr_one; [ $outer:expr ] ( $($args:tt)* ) ) => { $outer.expr_apply(
        vcx!(),
        $crate::expr_inner!(@expr_args; $($args)*),
    ) };
    (@expr_one; [ $outer:expr ] ) => { $outer.expr(vcx!()) };
    (@expr_one; ( $($lhs:tt)+ ) == ( $($rhs:tt)+ )) => { vcx!().mk_eq_expr(
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ) };
    (@expr_one; ( $($lhs:tt)+ ) && ( $($rhs:tt)+ )) => { vcx!().mk_conj(&[
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ]) };
    (@expr_one; ( $($lhs:tt)+ ) || ( $($rhs:tt)+ )) => { vcx!().mk_disj(&[
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ]) };
    (@expr_one; ( $($lhs:tt)+ ) == > ( $($rhs:tt)+ )) => { $crate::CastType::downcast_ty::<$crate::Bool>(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::Implies,
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    )) };
    (@expr_one; ( $($lhs:tt)+ ) <= ( $($rhs:tt)+ )) => { $crate::CastType::downcast_ty::<$crate::Bool>(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::CmpLe,
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    )) };
    (@expr_one; ( $($lhs:tt)+ ) < ( $($rhs:tt)+ )) => { $crate::CastType::downcast_ty::<$crate::Bool>(vcx!().mk_bin_op_expr(
        $crate::BinOpKind::CmpLt,
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    )) };
    (@expr_one; ( $($lhs:tt)+ ) + ( $($rhs:tt)+ )) => { vcx!().mk_bin_op_expr(
        $crate::BinOpKind::Add,
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ) };
    (@expr_one; ( $($lhs:tt)+ ) in ( $($rhs:tt)+ )) => { vcx!().mk_set_in_expr(
        $crate::expr_inner!(@expr_one; $($lhs)*),
        $crate::expr_inner!(@expr_one; $($rhs)*),
    ) };
    (@expr_one; null) => { vcx!().mk_null() };
    (@expr_one; true) => { vcx!().mk_bool::<true>() };
    (@expr_one; false) => { vcx!().mk_bool::<false>() };
    (@expr_one; result: $t:tt) => { vcx!().mk_result($crate::vir_type!(vcx!(); $t)) };
    (@expr_one; forall $($tokens:tt)+) => { {
        let mut qvars = Vec::<$crate::LocalDeclDyn>::new();
        $crate::expr_inner!(@forall_qvars(qvars); , $($tokens)*)
    } };
    (@expr_one; $ident:ident) => { $ident.expr(vcx!()) };
    (@expr_one; $($tokens:tt)*) => { compile_error!(concat!("VIR malformed expression: `" , stringify!($($tokens)*), "`")) };

    (@expr_tuple; ( $($inner:tt)+ )) => { $crate::expr_inner!(@expr_one; $($inner)*) };
    (@expr_tuple; [ $($inner:tt)* ]) => { $crate::expr_inner!(@expr_list; $($inner)*) };
    // This case lets us use `[fn](..[&args_vec])` instead of `[fn]([..[&args_vec]])`
    (@expr_tuple; ..[ $args:expr ]) => {
        $args
    };
    (@expr_tuple; $($other:tt)+ ) => { $crate::expr_inner!(@expr_one; $($other)*) };

    (@expr_args; $one:tt , $two:tt , $three:tt , $four:tt , $five:tt, $six:tt, $seven:tt, $eight:tt , $($tail:tt)+ ) => {
        compile_error!(concat!("VIR malformed arg, only up to 8 args supported: `", stringify!($one, $two, $three, $four, $five, $six, $seven, $eight), "`, but have tail: `", stringify!($($tail)*), "`"))
    };
    (@expr_args; $one:tt , $two:tt , $three:tt , $four:tt , $five:tt, $six:tt, $seven:tt, $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $three), $crate::expr_inner!(@expr_tuple; $four), $crate::expr_inner!(@expr_tuple; $five), $crate::expr_inner!(@expr_tuple; $six), $crate::expr_inner!(@expr_tuple; $seven), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $two:tt , $three:tt , $four:tt , $five:tt, $six:tt, $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $three), $crate::expr_inner!(@expr_tuple; $four), $crate::expr_inner!(@expr_tuple; $five), $crate::expr_inner!(@expr_tuple; $six), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $two:tt , $three:tt , $four:tt , $five:tt, $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $three), $crate::expr_inner!(@expr_tuple; $four), $crate::expr_inner!(@expr_tuple; $five), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $two:tt , $three:tt , $four:tt , $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $three), $crate::expr_inner!(@expr_tuple; $four), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $two:tt , $three:tt , $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $three), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $two:tt , $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $two), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $one:tt , $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $one), $crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; $($tail:tt)+ ) => {
        ($crate::expr_inner!(@expr_tuple; $($tail)*),)
    };
    (@expr_args; ) => { () };
    (@expr_args; $tokens:tt*) => {
        compile_error!(concat!("VIR malformed arg: `" , stringify!($($tokens)*), "`. Expected `ident/(...)` for single arg or `[...]` for many args"))
    };

    (@expr_list; ) => { Vec::<$crate::Expr<_>>::new().as_slice() };
    (@expr_list; $($args:tt)+ ) => {
        $crate::expr_inner!(@expr_iter; , $($args)*).collect::<Vec<$crate::Expr<_>>>().as_slice()
    };

    (@expr_iter; ) => { [].into_iter() };
    (@expr_iter; , ( $($first:tt)+ ) $($rest:tt)*) => { [$crate::expr_inner!(@expr_one; $($first)*)].into_iter().chain($crate::expr_inner!(@expr_iter; $($rest)*)) };
    (@expr_iter; ,   $ident:ident    $($rest:tt)*) => { [$crate::expr_inner!(@expr_one; $ident)].into_iter().chain($crate::expr_inner!(@expr_iter; $($rest)*)) };
    (@expr_iter; , ..[ $outer:expr ] ) => { $outer.iter().map(|e| e.expr(vcx!())) };
    (@expr_iter; , $($last:tt)+) => { [$crate::expr_inner!(@expr_one; $($last)*)].into_iter() };
    (@expr_iter; $($tokens:tt)+) => { compile_error!(concat!("VIR malformed expression list: `" , stringify!($($tokens)*), "`")) };

    (@forall_qvars($qvars:ident); :: $({ $($triggers:tt)+ })+ $($tokens:tt)+) => { vcx!().mk_forall_expr(
        vcx!().alloc_slice($qvars.as_slice()),
        vcx!().alloc_slice(
            [$($crate::expr_inner!(@expr_list; $($triggers)*)),*].into_iter()
                .map(|e: &[$crate::Expr<_>]| vcx!().mk_trigger(e))
                .collect::<Vec<_>>().as_slice()
        ),
        $crate::expr_inner!(@expr_one; $($tokens)*),
    ) };
    (@forall_qvars($qvars:ident); :: $($tokens:tt)*) => { compile_error!(concat!("VIR missing triggers or body: `" , stringify!($($tokens)*), "`")) };

    (@forall_qvars($qvars:ident); , ..[$outer:ident] $($tokens:tt)*) => { {
        $qvars.extend($outer.iter().map(|local| $crate::CastType::as_dyn(vcx!().mk_local_decl_local(local))));
        let $outer: Vec<$crate::ExprGen<_, _, _>> = $outer.iter().map(|local| vcx!().mk_local_ex_local(local)).collect();
        $crate::expr_inner!(@forall_qvars($qvars); $($tokens)*)
    } };
    (@forall_qvars($qvars:ident); , $qvar:ident : $qtype:tt $($tokens:tt)* ) => { {
        let local = vcx!().mk_local_decl(stringify!($qvar), $crate::vir_type!(vcx!(); $qtype));
        $qvars.push($crate::CastType::as_dyn(local));
        let $qvar: $crate::Expr<_> = vcx!().mk_local_ex(local);
        $crate::expr_inner!(@forall_qvars($qvars); $($tokens)*)
    } };
    (@forall_qvars($qvars:ident); $($tokens:tt)*) => { compile_error!(concat!("VIR malformed quantifier: `" , stringify!($($tokens)*), "`")) };
}
