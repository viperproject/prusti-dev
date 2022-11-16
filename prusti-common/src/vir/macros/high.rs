#[macro_export]
macro_rules! vir_high_type {
    (Int) => {$crate::vir::vir_high::Type::Int};
    (Bool) => {$crate::vir::vir_high::Type::Bool};
    ({$ty:expr}) => { $ty }
}

#[macro_export]
macro_rules! vir_high_local {
    ($name:ident : $type:tt) => {
        $crate::vir::vir_high::VariableDecl {
            name: stringify!($name).to_string(),
            ty: $crate::vir_type!($type)
        }
    }
}

#[macro_export]
macro_rules! vir_high_expr {
    (true) => {
        (true.into())
    };
    (false) => {
        (false.into())
    };

    ($lhs: tt == $rhs: tt) => {
        $crate::vir::vir_high::Expression::eq_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt != $rhs: tt) => {
        $crate::vir::vir_high::Expression::ne_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($head: tt && $tail: tt) => {
        $crate::vir::vir_high::Expression::and(vir_expr!($head), vir_expr!($tail))
    };
    ($head: tt || $tail: tt) => {
        $crate::vir::vir_high::Expression::or(vir_expr!($head), vir_expr!($tail))
    };
    ($lhs: tt > $rhs: tt) => {
        $crate::vir::vir_high::Expression::gt_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt >= $rhs: tt) => {
        $crate::vir::vir_high::Expression::ge_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt < $rhs: tt) => {
        $crate::vir::vir_high::Expression::lt_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt <= $rhs: tt) => {
        $crate::vir::vir_high::Expression::le_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };

    ($lhs: tt + $rhs: tt) => {
        $crate::vir::vir_high::Expression::add(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt - $rhs: tt) => {
        $crate::vir::vir_high::Expression::sub(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt * $rhs: tt) => {
        $crate::vir::vir_high::Expression::mul(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt / $rhs: tt) => {
        $crate::vir::vir_high::Expression::div(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt % $rhs: tt) => {
        $crate::vir::vir_high::Expression::modulo(vir_expr!($lhs), vir_expr!($rhs))
    };

    ($antecedent: tt ==> $consequent: tt) => {
        $crate::vir::vir_high::Expression::implies(vir_expr!($antecedent), vir_expr!($consequent))
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        $crate::vir::vir_high::Expression::magic_wand(vir_expr!($lhs), vir_expr!($rhs), $borrow)
    };

    // (forall $($name: ident : $type: tt),+ :: {$($triggers: tt),*} $body: tt) => {
    //     $crate::vir::vir_high::Expression::forall(
    //         vec![$($crate::vir_local!($name: $type)),+],
    //         vec![$($crate::vir::vir_high::Trigger::new(vec![vir_high_expr!($triggers)])),*],
    //         vir_high_expr!($body),
    //     )
    // };
    ([ $e: expr ]) => { $e.clone() };
    (( $($tokens: tt)+ )) => { vir_high_expr!($($tokens)+) }
}

// #[cfg(test)]
// mod tests {
//     use super::*;
//     use crate::vir::vir_high::*;

//     #[test]
//     fn forall() {
//         let expected = Expr::ForAll( ForAll {
//             variables: vec![vir_high_local!(i: Int), vir_high_local!(j: Int)],
//             triggers: vec![Trigger::new(vec![vir_high_expr!{ true }]), Trigger::new(vec![vir_high_expr!{ false }])],
//             body: Box::new(vir_high_expr!{ true }),
//             position: Position::default(),
//         });

//         let actual = vir_high_expr!{ forall i: Int, j: Int :: {true, false} true };

//         assert_eq!(expected, actual);
//     }

//     #[test]
//     fn expr_passthrough() {
//         let expr = vir_high_stmt!{ assert true };

//         assert_eq!(expr, vir_high_expr!{ [expr] });
//         assert_eq!(expr, vir_high_expr!{ ( [expr] ) });
//     }
// }
