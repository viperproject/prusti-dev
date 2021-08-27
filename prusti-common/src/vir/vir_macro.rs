#[macro_export]
macro_rules! vir_type {
    (Int) => {$crate::vir::polymorphic_vir::Type::Int};
    (Bool) => {$crate::vir::polymorphic_vir::Type::Bool};
    ({$ty:expr}) => { $ty }
}

#[macro_export]
macro_rules! vir_local {
    ($name:ident : $type:tt) => {
        $crate::vir::polymorphic_vir::LocalVar {
            name: stringify!($name).to_string(),
            typ: $crate::vir_type!($type)
        }
    }
}

#[macro_export]
macro_rules! vir_stmt {
    (# $comment: expr) => {
        $crate::vir::polymorphic_vir::Stmt::comment($comment)
    };
    (label $label: expr) => {
        $crate::vir::polymorphic_vir::Stmt::label($label)
    };
    (assert $exp: tt) => {
        $crate::vir::polymorphic_vir::Stmt::Assert( $crate::vir::polymorphic_vir::Assert {
            expr: vir_expr!($exp),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };
    (inhale $exp: tt) => {
        $crate::vir::polymorphic_vir::Stmt::Inhale( $crate::vir::polymorphic_vir::Inhale {
            expr: vir_expr!($exp),
        })
    };
    (exhale $exp: tt) => {
        $crate::vir::polymorphic_vir::Stmt::Exhale( $crate::vir::polymorphic_vir::Exhale {
            expr: vir_expr!($exp),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };
    (apply $exp: tt) => {
        $crate::vir::polymorphic_vir::Stmt::ApplyMagicWand( $crate::vir::polymorphic_vir::ApplyMagicWand {
            magic_wand: vir_expr!($exp),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };
    (obtain $exp: tt) => {
        $crate::vir::polymorphic_vir::Stmt::Obtain( $crate::vir::polymorphic_vir::Obtain {
            expr: vir_expr!($exp),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };
    (if ($exp: tt) { $($then: tt);* } else { $($elze: tt);* }) => {
        $crate::vir::polymorphic_vir::Stmt::If( $crate::vir::polymorphic_vir::If {
            guard: vir_expr!($exp),
            then_stmts: vec![$(vir_stmt!($then)),*],
            else_stmts: vec![$(vir_stmt!($elze)),*],
        })
    };
    (if ($exp: tt) { $($then: tt);* }) => {
        $crate::vir::polymorphic_vir::Stmt::If( $crate::vir::polymorphic_vir::If {
            guard: vir_expr!($exp),
            then_stmts: vec![$(vir_expr!($then)),*],
            else_stmts: vec![],
        })
    };
}

#[macro_export]
macro_rules! vir_expr {
    (true) => {
        $crate::vir::polymorphic_vir::Expr::Const( $crate::vir::polymorphic_vir::ConstExpr {
            value: $crate::vir::polymorphic_vir::Const::Bool(true),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };
    (false) => {
        $crate::vir::polymorphic_vir::Expr::Const( $crate::vir::polymorphic_vir::ConstExpr {
            value: $crate::vir::polymorphic_vir::Const::Bool(false),
            position: $crate::vir::polymorphic_vir::Position::default(),
        })
    };

    ($lhs: tt == $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::eq_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt != $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::ne_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($head: tt && $tail: tt) => {
        $crate::vir::polymorphic_vir::Expr::and(vir_expr!($head), vir_expr!($tail))
    };
    ($head: tt || $tail: tt) => {
        $crate::vir::polymorphic_vir::Expr::or(vir_expr!($head), vir_expr!($tail))
    };
    ($lhs: tt > $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::gt_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt >= $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::ge_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt < $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::lt_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt <= $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::le_cmp(vir_expr!($lhs), vir_expr!($rhs))
    };

    ($lhs: tt + $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::add(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt - $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::sub(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt * $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::mul(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt / $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::div(vir_expr!($lhs), vir_expr!($rhs))
    };
    ($lhs: tt % $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::modulo(vir_expr!($lhs), vir_expr!($rhs))
    };

    ($antecedent: tt ==> $consequent: tt) => {
        $crate::vir::polymorphic_vir::Expr::implies(vir_expr!($antecedent), vir_expr!($consequent))
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        $crate::vir::polymorphic_vir::Expr::magic_wand(vir_expr!($lhs), vir_expr!($rhs), $borrow)
    };

    (forall $($name: ident : $type: tt),+ :: {$($triggers: tt),*} $body: tt) => {
        $crate::vir::polymorphic_vir::Expr::forall(
            vec![$($crate::vir_local!($name: $type)),+],
            vec![$($crate::vir::polymorphic_vir::Trigger::new(vec![vir_expr!($triggers)])),*],
            vir_expr!($body),
        )
    };
    ([ $e: expr ]) => { $e.clone() };
    (( $($tokens: tt)+ )) => { vir_expr!($($tokens)+) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vir::polymorphic_vir::*;

    #[test]
    fn forall() {
        let expected = Expr::ForAll( ForAll {
            variables: vec![vir_local!(i: Int), vir_local!(j: Int)],
            triggers: vec![Trigger::new(vec![vir_expr!{ true }]), Trigger::new(vec![vir_expr!{ false }])],
            body: Box::new(vir_expr!{ true }),
            position: Position::default(),
        });

        let actual = vir_expr!{ forall i: Int, j: Int :: {true, false} true };

        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_passthrough() {
        let expr = vir_stmt!{ assert true };

        assert_eq!(expr, vir_expr!{ [expr] });
        assert_eq!(expr, vir_expr!{ ( [expr] ) });
    }
}
