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
    ($vcx:expr; [ $name:expr ]) => { $name };
    ($vcx:expr; $name:ident ) => { $vcx.alloc_str(stringify!($name)) };
}

#[macro_export]
macro_rules! vir_format {
    ($vcx:expr, $($arg:tt)*) => { $vcx.alloc_str(&format!($($arg)*)) };
}

#[macro_export]
macro_rules! vir_type {
    ($vcx:expr; Bool) => { & $crate::TypeData::Bool };
    ($vcx:expr; Ref) => { & $crate::TypeData::Ref };
    ($vcx:expr; Uint($bit_width:expr)) => { $vcx.alloc($crate::TypeData::Int { signed: false, bit_width: $bit_width }) };
    ($vcx:expr; Int($bit_width:expr)) => { $vcx.alloc($crate::TypeData::Int { signed: true, bit_width: $bit_width }) };
    ($vcx:expr; [ $ty:expr ]) => { $ty };
    ($vcx:expr; $name:ident) => {
        $vcx.alloc($crate::TypeData::Domain($vcx.alloc_str(stringify!($name))))
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
        let val_ex = $vcx.mk_local_ex("val");
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
        $vcx.alloc($crate::DomainFunctionData {
            unique: true,
            name: $name.name(),
            args: $crate::vir_type_list!($vcx; $($args)*),
            ret: $crate::vir_type!($vcx; $ret),
        })
    }};
    ($vcx:expr; function $name:tt ( $( $args:tt )* ): $ret:tt ) => {{
        $vcx.alloc($crate::DomainFunctionData {
            unique: false,
            name: $name.name(),
            args: $crate::vir_type_list!($vcx; $($args)*),
            ret: $crate::vir_type!($vcx; $ret),
        })
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
            $crate::vir_ident!($vcx; $name),
            &[],
            $vcx.alloc_slice(&axioms),
            $vcx.alloc_slice(&functions),
        )
    }};
}

#[macro_export]
macro_rules! vir_predicate {
    ($vcx:expr; predicate $name:tt ( $( $args:tt )* ) { [$expr:expr] }) => {{
        $vcx.mk_predicate(
            $crate::vir_ident!($vcx; $name),
            $crate::vir_arg_list!($vcx; $($args)*),
            Some($expr)
        )
    }};
    ($vcx:expr; predicate $name:tt ( $( $args:tt )* )) => {{
        $vcx.mk_predicate(
            $crate::vir_ident!($vcx; $name),
            $crate::vir_arg_list!($vcx; $($args)*),
            None
        )
    }};
}
