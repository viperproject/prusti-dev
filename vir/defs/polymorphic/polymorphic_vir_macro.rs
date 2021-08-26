#[macro_export]
macro_rules! vir_type {
    (Int) => {$crate::polymorphic::Type::Int};
    (Bool) => {$crate::polymorphic::Type::Bool};
    ({$ty:expr}) => { $ty }
}

#[macro_export]
macro_rules! vir_local {
    ($name:ident : $type:tt) => {
        $crate::polymorphic::LocalVar {
            name: stringify!($name).to_string(),
            typ: vir_type!($type)
        }
    }
}

#[macro_export]
macro_rules! vir {
    (# $comment: expr) => {
        $crate::polymorphic::Stmt::comment($comment)
    };
    (label $label: expr) => {
        $crate::polymorphic::Stmt::label($label)
    };
    (assert $exp: tt) => {
        $crate::polymorphic::Stmt::Assert( $crate::polymorphic::Assert {
            expr: vir!($exp),
            position: $crate::polymorphic::Position::default(),
        })
    };
    (inhale $exp: tt) => {
        $crate::polymorphic::Stmt::Inhale( $crate::polymorphic::Inhale {
            expr: vir!($exp),
        })
    };
    (exhale $exp: tt) => {
        $crate::polymorphic::Stmt::Exhale( $crate::polymorphic::Exhale {
            expr: vir!($exp),
            position: $crate::polymorphic::Position::default(),
        })
    };
    (apply $exp: tt) => {
        $crate::polymorphic::Stmt::ApplyMagicWand( $crate::polymorphic::ApplyMagicWand {
            magic_wand: vir!($exp),
            position: $crate::polymorphic::Position::default(),
        })
    };
    (obtain $exp: tt) => {
        $crate::polymorphic::Stmt::Obtain( $crate::polymorphic::Obtain {
            expr: vir!($exp),
            position: $crate::polymorphic::Position::default(),
        })
    };
    (if ($exp: tt) { $($then: tt);* } else { $($elze: tt);* }) => {
        $crate::polymorphic::Stmt::If( $crate::polymorphic::If {
            guard: vir!($exp),
            then_stmts: vec![$(vir!($then)),*],
            else_stmts: vec![$(vir!($elze)),*],
        })
    };
    (if ($exp: tt) { $($then: tt);* }) => {
        $crate::polymorphic::Stmt::If( $crate::polymorphic::If {
            guard: vir!($exp),
            then_stmts: vec![$(vir!($then)),*],
            else_stmts: vec![],
        })
    };
    (true) => {
        $crate::polymorphic::Expr::Const( $crate::polymorphic::ConstExpr {
            value: $crate::polymorphic::Const::Bool(true),
            position: $crate::polymorphic::Position::default(),
        })
    };
    (false) => {
        $crate::polymorphic::Expr::Const( $crate::polymorphic::ConstExpr {
            value: $crate::polymorphic::Const::Bool(false),
            position: $crate::polymorphic::Position::default(),
        })
    };

    ($lhs: tt == $rhs: tt) => {
        $crate::polymorphic::Expr::eq_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt != $rhs: tt) => {
        $crate::polymorphic::Expr::ne_cmp(vir!($lhs), vir!($rhs))
    };
    ($head: tt && $tail: tt) => {
        $crate::polymorphic::Expr::and(vir!($head), vir!($tail))
    };
    ($head: tt || $tail: tt) => {
        $crate::polymorphic::Expr::or(vir!($head), vir!($tail))
    };
    ($lhs: tt > $rhs: tt) => {
        $crate::polymorphic::Expr::gt_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt >= $rhs: tt) => {
        $crate::polymorphic::Expr::ge_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt < $rhs: tt) => {
        $crate::polymorphic::Expr::lt_cmp(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt <= $rhs: tt) => {
        $crate::polymorphic::Expr::le_cmp(vir!($lhs), vir!($rhs))
    };

    ($lhs: tt + $rhs: tt) => {
        $crate::polymorphic::Expr::add(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt - $rhs: tt) => {
        $crate::polymorphic::Expr::sub(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt * $rhs: tt) => {
        $crate::polymorphic::Expr::mul(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt / $rhs: tt) => {
        $crate::polymorphic::Expr::div(vir!($lhs), vir!($rhs))
    };
    ($lhs: tt % $rhs: tt) => {
        $crate::polymorphic::Expr::modulo(vir!($lhs), vir!($rhs))
    };

    ($antecedent: tt ==> $consequent: tt) => {
        $crate::polymorphic::Expr::implies(vir!($antecedent), vir!($consequent))
    };
    ($lhs: tt {$borrow: expr} --* $rhs: tt) => {
        $crate::polymorphic::Expr::magic_wand(vir!($lhs), vir!($rhs), $borrow)
    };

    (forall $($name: ident : $type: tt),+ :: {$($triggers: tt),*} $body: tt) => {
        $crate::polymorphic::Expr::forall(
            vec![$(vir_local!($name: $type)),+],
            vec![$($crate::polymorphic::Trigger::new(vec![vir!($triggers)])),*],
            vir!($body),
        )
    };
    ([ $e: expr ]) => { $e.clone() };
    (( $($tokens: tt)+ )) => { vir!($($tokens)+) }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::polymorphic::*;

    #[test]
    fn forall() {
        let expected = Expr::ForAll( ForAll {
            variables: vec![vir_local!(i: Int), vir_local!(j: Int)],
            triggers: vec![Trigger::new(vec![vir!{ true }]), Trigger::new(vec![vir!{ false }])],
            body: Box::new(vir!{ true }),
            position: Position::default(),
        });

        let actual = vir!{ forall i: Int, j: Int :: {true, false} true };

        assert_eq!(expected, actual);
    }

    #[test]
    fn expr_passthrough() {
        let expr = vir!{ assert true };

        assert_eq!(expr, vir!{ [expr] });
        assert_eq!(expr, vir!{ ( [expr] ) });
    }
}
