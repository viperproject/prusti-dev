use super::*;

vir_raw_block! { AssumeAssertHelpers =>
    impl crate::common::statement::AssumeAssertHelpers for Statement {
        type Statement = Statement;
        type Expression = Expression;
        type LabelSymbol = LabelSymbol;
        fn assume(assertion: Expression) -> Statement {
            Statement::Assume(Assume {
                assertion, label: None,
            })
        }
        fn assume_with_label(assertion: Expression, label: LabelSymbol) -> Statement {
            Statement::Assume(Assume {
                assertion, label: Some(label),
            })
        }
        fn assert(assertion: Expression) -> Statement {
            Statement::Assert(Assert {
                assertion, label: None,
            })
        }
        fn assert_with_label(assertion: Expression, label: LabelSymbol) -> Statement {
            Statement::Assert(Assert {
                assertion, label: Some(label),
            })
        }
    }
}
