pub macro ty {
    (Int) => {$crate::low::ast::ty::Type::Int},
    (Float32) => {$crate::low::ast::ty::Type::Float(crate::low::ast::ty::Float::F32)},
    (Float64) => {$crate::low::ast::ty::Type::Float(crate::low::ast::ty::Float::F64)},
    (Bool) => {$crate::low::ast::ty::Type::Bool},
    (Perm) => {$crate::low::ast::ty::Type::Perm},
    (Place) => {$crate::low::ast::ty::Type::domain("Place".to_string())},
    (Address) => {$crate::low::ast::ty::Type::domain("Address".to_string())},
    (Lifetime) => {$crate::low::ast::ty::Type::domain("Lifetime".to_string())},
    (Bytes) => {$crate::low::ast::ty::Type::domain("Bytes".to_string())},
    ({$ty:expr}) => { $ty },
}

pub macro var($name:ident : $type:tt) {
    $crate::low::ast::variable::VariableDecl::new(
        stringify!($name),
        $crate::low::macros::ty!($type),
    )
}

pub macro vars {
    ( $( $name:ident : $type:tt ),* ) => {
        vec![
            $( $crate::low::macros::var!($name: $type), )*
        ]
    }
}

pub macro var_decls {
    ( $( $name:ident : $type:tt ),* ) => {
        $( let $name = $crate::low::macros::var!($name: $type); )*
    }
}

pub macro method_name( $method_name:ident<$ty:tt> ) {
    format!(
        "{}${}",
        stringify!($method_name),
        $crate::common::identifier::WithIdentifier::get_identifier($ty)
    )
}

pub macro predicate_name( $method_name:ident<$ty:tt> ) {
    $crate::low::macros::method_name!($method_name<$ty>)
}

pub macro expr {
    (true) => {
        $crate::low::ast::expression::Expression::constant_no_pos(
            $crate::low::ast::expression::ConstantValue::Bool(true),
            $crate::low::ast::ty::Type::Bool,
        )
    },
    (false) => {
        $crate::low::ast::expression::Expression::constant_no_pos(
            $crate::low::ast::expression::ConstantValue::Bool(false),
            $crate::low::ast::ty::Type::Bool,
        )
    },
    ( acc($predicate_name:ident<$ty:tt>(
        $($argument:tt),*
        $(; $argument_list:ident )?
    )) ) => {
        {
            let mut arguments = vec![ $( $crate::low::macros::expr!( $argument ) ),* ];
            $( arguments.extend($argument_list.clone()); )?
            $crate::low::ast::expression::Expression::predicate_access_predicate_no_pos(
                format!(
                    "{}${}",
                    stringify!($predicate_name),
                    $crate::common::identifier::WithIdentifier::get_identifier($ty)
                ),
                arguments,
                $crate::low::ast::expression::Expression::full_permission(),
            )
        }
    },
    ( acc($predicate_name:ident<$ty:tt>( $($argument:tt),* $(; $argument_list:ident )?), $perm:tt) ) => {
        {
            let mut arguments = vec![ $( $crate::low::macros::expr!( $argument ) ),* ];
            $( arguments.extend($argument_list); )?
            $crate::low::ast::expression::Expression::predicate_access_predicate_no_pos(
                format!(
                    "{}${}",
                    stringify!($predicate_name),
                    $crate::common::identifier::WithIdentifier::get_identifier($ty)
                ),
                arguments,
                $crate::low::macros::expr!( $perm ),
            )
        }
    },
    ( acc($predicate_name:ident( $($argument:tt),* ), $perm:tt) ) => {
        $crate::low::ast::expression::Expression::predicate_access_predicate_no_pos(
            stringify!($predicate_name).to_string(),
            vec![ $( $crate::low::macros::expr!( $argument ) ),* ],
            $crate::low::macros::expr!( $perm ),
        )
    },
    ( acc($predicate_name:ident( $($argument:tt),* )) ) => {
        $crate::low::ast::expression::Expression::predicate_access_predicate_no_pos(
            stringify!($predicate_name).to_string(),
            vec![ $( $crate::low::macros::expr!( $argument ) ),* ],
            $crate::low::ast::expression::Expression::full_permission(),
        )
    },
    ( old( $argument:tt ) ) => {
        $crate::low::ast::expression::Expression::labelled_old_no_pos(
            None,
            expr!( $argument ),
        )
    },
    ( forall( $( $var_name:ident : $var_type:tt ),* :: $( raw_code { $( $statement:stmt; )+ } )? [$( { $( $trigger:tt ),+ } ),*] $($body: tt)+ ) ) => {
        {
            $( let $var_name = $crate::low::macros::var! { $var_name: $var_type }; )*
            $( $( $statement; )+ )?
            $crate::low::ast::expression::Expression::quantifier_no_pos(
                $crate::low::ast::expression::QuantifierKind::ForAll,
                vec![ $( $var_name.clone() ),* ],
                vec![
                    $(
                        $crate::low::ast::expression::Trigger::new(
                            vec![
                                $( $crate::low::macros::expr!($trigger) ),+
                            ]
                        )
                    ),*
                ],
                $crate::low::macros::expr!($($body)+)
            )
        }
    },
    ( wand( $lhs:tt --* $rhs:tt ) ) => {
        $crate::low::ast::expression::Expression::magic_wand_no_pos(
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
        )
    },
    ( $domain_name:ident <$ty:tt> :: $function_name:ident( $($argument:tt),* ) ) => {
        $crate::low::ast::expression::Expression::domain_function_call(
            format!(
                "{}${}",
                stringify!($domain_name),
                $crate::common::identifier::WithIdentifier::get_identifier($ty)
            ),
            format!(
                "{}${}",
                stringify!($function_name),
                $crate::common::identifier::WithIdentifier::get_identifier($ty)
            ),
            vec![ $( expr!( $argument ) ),* ],
            $function_name.clone(),
        )
    },
    ( $domain_name:ident :: $function_name:ident( $($argument:tt),* ) ) => {
        $crate::low::ast::expression::Expression::domain_function_call(
            stringify!($domain_name),
            stringify!($function_name),
            vec![ $( expr!( $argument ) ),* ],
            $function_name.clone(),
        )
    },
    ( $function_name:ident( $($argument:tt),* ) ) => {
        $crate::low::ast::expression::Expression::function_call(
            stringify!($function_name).to_string(),
            vec![ $( expr!( $argument ) ),* ],
            $function_name.clone(),
        )
    },
    ( $variable:ident ) => {
        $crate::low::ast::expression::Expression::local_no_pos(
            $variable.clone()
        )
    },
    (!$arg: tt) => {
        $crate::low::ast::expression::Expression::unary_op(
            $crate::low::ast::expression::UnaryOpKind::Not,
            $crate::low::macros::expr!( $arg ),
            Default::default(),
        )
    },
    (-$arg: tt) => {
        $crate::low::ast::expression::Expression::unary_op(
            $crate::low::ast::expression::UnaryOpKind::Minus,
            $crate::low::macros::expr!( $arg ),
            Default::default(),
        )
    },
    ($lhs: tt ==> $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::Implies,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt == $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::EqCmp,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt != $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::NeCmp,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt <= $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::LeCmp,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt < $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::LtCmp,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt * $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::Mul,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt subset $rhs: tt) => {
        {
            let lhs = $crate::low::macros::expr!( $lhs );
            $crate::low::ast::expression::Expression::container_op(
                $crate::low::ast::expression::ContainerOpKind::SetSubset,
                ($crate::low::operations::ty::Typed::get_type(&lhs).clone()),
                vec![lhs, $crate::low::macros::expr!( $rhs )],
                Default::default(),
            )
        }
    },
    ($lhs: tt in $rhs: tt) => {
        {
            let lhs = $crate::low::macros::expr!( $lhs );
            $crate::low::ast::expression::Expression::container_op(
                $crate::low::ast::expression::ContainerOpKind::SetContains,
                ($crate::low::operations::ty::Typed::get_type(&lhs).clone()),
                vec![lhs, $crate::low::macros::expr!( $rhs )],
                Default::default(),
            )
        }
    },
    ($lhs: tt || $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::Or,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($lhs: tt && $rhs: tt) => {
        $crate::low::ast::expression::Expression::binary_op(
            $crate::low::ast::expression::BinaryOpKind::And,
            $crate::low::macros::expr!( $lhs ),
            $crate::low::macros::expr!( $rhs ),
            Default::default(),
        )
    },
    ($arg1: tt && $arg2: tt $(&& $arg3: tt)+) => {
        {
            let mut expression = $crate::low::macros::expr!{ ($arg1 && $arg2) };
            $(expression = $crate::low::macros::expr!{ ([expression] && $arg3) };)+
            expression
        }
    },
    ([ $e: expr ]) => { $e },
    (( $($tokens: tt)+ )) => { $crate::low::macros::expr!($($tokens)+) },
}

/// An expression with position
pub macro exprp {
    ($position:expr => $($tokens:tt)+ ) => {
        {
            let expression = $crate::low::macros::expr!($($tokens)+);
            expression.set_default_position($position)
        }
    },
}

pub macro stmt {
    (# $comment: expr) => {
        $crate::low::ast::statement::Statement::comment($comment)
    },
    (assume $expr:tt) => {
        $crate::low::ast::statement::Statement::assume_no_pos(
            $crate::low::macros::expr!($expr)
        )
    },
    (assert $expr:tt) => {
        $crate::low::ast::statement::Statement::assert_no_pos(
            $crate::low::macros::expr!($expr)
        )
    },
    (inhale $expr:tt) => {
        $crate::low::ast::statement::Statement::inhale_no_pos(
            $crate::low::macros::expr!($expr)
        )
    },
    (exhale $expr:tt) => {
        $crate::low::ast::statement::Statement::exhale_no_pos(
            $crate::low::macros::expr!($expr)
        )
    },
    (call<$condition:ident> $method_name:ident<$ty:tt>( $($argument:tt),* $(; $arguments:tt )? )) => {{
        $crate::low::ast::statement::Statement::conditional_no_pos(
            $condition,
            vec![
                $crate::low::macros::stmt!{ call $method_name<$ty>( $($argument),* $(; $arguments )? ) }
            ],
            Vec::new(),
        )
    }},
    (call $method_name:ident<$ty:tt>( $($argument:tt),*  $(; $arguments:tt )? )) => {{
        let mut argument_expressions =  vec![ $( $crate::low::macros::expr!( $argument ) ),* ];
        $(argument_expressions.extend($arguments);)?
        $crate::low::ast::statement::Statement::method_call_no_pos(
            $crate::low::macros::method_name!{ $method_name<$ty> },
            argument_expressions,
            Vec::new(),
        )
    }},
    (fold<$condition:ident> $predicate_name:ident<$ty:tt>(
        $($argument:tt),*
        $(; $argument_list:ident )?
    )) => {
        $crate::low::ast::statement::Statement::conditional_no_pos(
            $condition,
            vec![
                $crate::low::macros::stmt!{ fold $predicate_name<$ty>( $($argument),* $(; $argument_list )? ) }
            ],
            Vec::new(),
        )
    },
    (fold acc(
        $predicate_name:ident<$ty:tt>(
            $($argument:tt),*
            $(; $argument_list:ident )?
        ),
        $permission_amount:tt
    )) => {
        $crate::low::ast::statement::Statement::fold_no_pos(
            $crate::low::macros::expr!(
                acc(
                    $predicate_name<$ty>( $($argument),* $(; $argument_list )? ),
                    $permission_amount
                )
            )
        )
    },
    (fold $predicate_name:ident<$ty:tt>(
        $($argument:tt),*
        $(; $argument_list:ident )?
    )) => {
        $crate::low::ast::statement::Statement::fold_no_pos(
            $crate::low::macros::expr!(acc($predicate_name<$ty>( $($argument),* $(; $argument_list )? )))
        )
    },
    (unfold<$condition:ident> $predicate_name:ident<$ty:tt>(
        $($argument:tt),*
        $(; $argument_list:ident )?
    )) => {
        $crate::low::ast::statement::Statement::conditional_no_pos(
            $condition,
            vec![
                $crate::low::macros::stmt!{ unfold $predicate_name<$ty>( $($argument),* $(; $argument_list )? ) }
            ],
            Vec::new(),
        )
    },
    (unfold acc(
        $predicate_name:ident<$ty:tt>(
            $($argument:tt),*
            $(; $argument_list:ident )?
        ),
        $permission_amount:tt
    )) => {
        $crate::low::ast::statement::Statement::unfold_no_pos(
            $crate::low::macros::expr!(
                acc(
                    $predicate_name<$ty>( $($argument),* $(; $argument_list )? ),
                    $permission_amount
                )
            )
        )
    },
    (unfold $predicate_name:ident<$ty:tt>(
        $($argument:tt),*
        $(; $argument_list:ident )?
    )) => {
        $crate::low::ast::statement::Statement::unfold_no_pos(
            $crate::low::macros::expr!(acc($predicate_name<$ty>( $($argument),* $(; $argument_list )? )))
        )
    },
    (apply<$condition:ident> $lhs:tt --* $rhs:tt) => {
        $crate::low::ast::statement::Statement::conditional_no_pos(
            $condition,
            vec![
                $crate::low::macros::stmt!{ apply $lhs --* $rhs }
            ],
            Vec::new(),
        )
    },
    (apply $lhs:tt --* $rhs:tt) => {
        $crate::low::ast::statement::Statement::apply_magic_wand_no_pos(
            $crate::low::macros::expr!{ wand( $lhs --* $rhs ) }
        )
    },
    ({ $($tokens: tt)+ }) => { $crate::low::macros::stmt!($($tokens)+) },
}

/// A statement with position
pub macro stmtp {
    ($position:expr => $($tokens:tt)+ ) => {
        {
            let statement = $crate::low::macros::stmt!($($tokens)+);
            statement.set_default_position($position)
        }
    },
}

pub macro stmts {
    ( $( $stmt:tt );* ) => {
        vec![
            $( $crate::low::macros::stmt!($stmt), )*
        ]
    }
}

pub macro method {
    (
        $kind:ident =>
        $method_name:ident<$ty:tt>( $( $parameter_name:ident : $parameter_type:tt ),* )
            returns ( $( $result_name:ident : $result_type:tt ),* )
        $( raw_code { $( $statement:stmt; )+ } )?
        $( requires $pre:tt; )*
        $( ensures $post:tt; )*
        {
            $( $stmt:tt );*
        }
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            $( let $result_name = $crate::low::macros::var! { $result_name: $result_type }; )*
            $( $( $statement; )+ )?
            $crate::low::cfg::method::MethodDecl::new(
                $crate::low::macros::method_name!{ $method_name<$ty> },
                $crate::low::cfg::method::MethodKind::$kind,
                vec![ $($parameter_name.clone()),* ],
                vec![ $($result_name.clone()),* ],
                vec![ $( $crate::low::macros::expr!( $pre ) ),* ],
                vec![ $( $crate::low::macros::expr!( $post ) ),* ],
                Some($crate::low::macros::stmts!{ $( $stmt );* }),
            )
        }
    },
    (
        $kind:ident =>
        $method_name:ident<$ty:tt>(
            $( $parameter_name:ident : $parameter_type:tt ),*
            $(,* $parameter_list:ident )?
        )
            returns ( $( $result_name:ident : $result_type:tt ),* )
        $( raw_code { $( $statement:stmt; )+ } )?
        $( requires $pre:tt; )*
        $( ensures $post:tt; )*
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            $( let $result_name = $crate::low::macros::var! { $result_name: $result_type }; )*
            $( $( $statement; )+ )?
            let mut parameters = vec![ $($parameter_name.clone()),* ];
            $( parameters.extend($parameter_list); )?
            $crate::low::cfg::method::MethodDecl::new(
                $crate::low::macros::method_name!{ $method_name<$ty> },
                $crate::low::cfg::method::MethodKind::$kind,
                parameters,
                vec![ $($result_name.clone()),* ],
                vec![ $( $crate::low::macros::expr!( $pre ) ),* ],
                vec![ $( $crate::low::macros::expr!( $post ) ),* ],
                None,
            )
        }
    },
}

pub macro function {
    (
        $kind:ident =>
        $function_name:ident(
            $( $parameter_name:ident : $parameter_type:tt ),*
        ): $result_type:tt
        $( requires $pre:tt; )*
        $( ensures $post:tt; )*
        { $body:tt }
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            let result = $crate::low::macros::var! { result: $result_type };
            $crate::low::ast::function::FunctionDecl::new(
                stringify!($function_name).to_string(),
                $crate::low::ast::function::FunctionKind::$kind,
                $crate::low::macros::vars!{ $( $parameter_name : $parameter_type ),* },
                $crate::low::macros::ty! { $result_type },
                vec![ $( $crate::low::macros::expr!( $pre ) ),* ],
                vec![ $( $crate::low::macros::expr!( $post ) ),* ],
                Some($crate::low::macros::expr!{$body}),
            )
        }
    },
    (
        $kind:ident =>
        $function_name:ident(
            $( $parameter_name:ident : $parameter_type:tt ),*
        ): $result_type:tt
        $( requires $pre:tt; )*
        $( ensures $post:tt; )*
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            let result = $crate::low::macros::var! { result: $result_type };
            $crate::low::ast::function::FunctionDecl::new(
                stringify!($function_name).to_string(),
                $crate::low::ast::function::FunctionKind::$kind,
                vars!{ $( $parameter_name : $parameter_type ),* },
                $crate::low::macros::ty! { $result_type },
                vec![ $( $crate::low::macros::expr!( $pre ) ),* ],
                vec![ $( $crate::low::macros::expr!( $post ) ),* ],
                None,
            )
        }
    },
}

pub macro predicate {
    (
        $predicate_name:ident<$ty:tt>( $( $parameter_name:ident : $parameter_type:tt ),* )
        { $body:tt }
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            $crate::low::ast::predicate::PredicateDecl::new(
                format!(
                    "{}${}",
                    stringify!($predicate_name),
                    $crate::common::identifier::WithIdentifier::get_identifier($ty)
                ),
                vec![ $($parameter_name.clone()),* ],
                Some($crate::low::macros::expr!{$body}),
            )
        }
    },
    (
        $predicate_name:ident<$ty:tt>(
            $( $parameter_name:ident : $parameter_type:tt ),*
            $(,* $parameter_list:ident )?
        )
        { $body:tt }
    ) => {
        {
            $( let $parameter_name = $crate::low::macros::var! { $parameter_name: $parameter_type }; )*
            let mut parameters = vec![ $($parameter_name.clone()),* ];
            $( parameters.extend($parameter_list); )?
            $crate::low::ast::predicate::PredicateDecl::new(
                format!(
                    "{}${}",
                    stringify!($predicate_name),
                    $crate::common::identifier::WithIdentifier::get_identifier($ty)
                ),
                parameters,
                Some($crate::low::macros::expr!{$body}),
            )
        }
    },
}
