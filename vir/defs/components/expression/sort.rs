trait Interface {
    type Context;
    type Sort;
}

use super::*;

vir_raw_block! { Variable =>
    impl<C: Context> WithSort<C> for Variable {
        fn sort<'a>(&'a self, context: &'a C) -> &'a Sort {
            context.get_variable_sort(&self.name)
        }
    }
}
vir_raw_block! { Constant =>
    impl<C: Context> WithSort<C> for Constant {
        fn sort<'a>(&'a self, _context: &'a C) -> &'a Sort {
            match self {
                Constant::Bool(_) => &Sort::Bool,
                Constant::Int(_) => &Sort::Int,
            }
        }
    }
}
vir_raw_block! { UnaryOperation =>
    impl<C: Context> WithSort<C> for UnaryOperation {
        fn sort<'a>(&'a self, context: &'a C) -> &'a Sort {
            self.arg.sort(context)
        }
    }
}
vir_raw_block! { BinaryOperation =>
    impl<C: Context> WithSort<C> for BinaryOperation {
        fn sort<'a>(&'a self, context: &'a C) -> &'a Sort {
            match self.kind {
                BinaryOperationKind::EqCmp
                | BinaryOperationKind::NeCmp
                | BinaryOperationKind::GtCmp
                | BinaryOperationKind::GeCmp
                | BinaryOperationKind::LtCmp
                | BinaryOperationKind::LeCmp
                | BinaryOperationKind::And
                | BinaryOperationKind::Or
                | BinaryOperationKind::Implies => &Sort::Bool,
                BinaryOperationKind::Add
                | BinaryOperationKind::Sub
                | BinaryOperationKind::Mul
                | BinaryOperationKind::Div
                | BinaryOperationKind::Mod => {
                    let sort = self.left.sort(context);
                    debug_assert_eq!(sort, self.right.sort(context));
                    sort
                },
            }
        }
    }
}
vir_raw_block! { Conditional =>
    impl<C: Context> WithSort<C> for Conditional {
        fn sort<'a>(&'a self, context: &'a C) -> &'a Sort {
            let sort = self.then_expr.sort(context);
            debug_assert_eq!(sort, self.else_expr.sort(context));
            sort
        }
    }
}
vir_raw_block! { Quantifier =>
    impl<C: Context> WithSort<C> for Quantifier {
        fn sort<'a>(&'a self, _context: &'a C) -> &'a Sort {
            &Sort::Bool
        }
    }
}
vir_raw_block! { FunctionApplication =>
    impl<C: Context> WithSort<C> for FunctionApplication {
        fn sort<'a>(&'a self, context: &'a C) -> &'a Sort {
            context.get_function_sort(&self.function)
        }
    }
}
vir_raw_block! { LabelledExpression =>
    impl<C: Context> WithSort<C> for LabelledExpression {
        fn sort<'a>(&'a self, _context: &'a C) -> &'a Sort {
            &Sort::Bool
        }
    }
}
