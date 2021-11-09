pub trait VariableHelpers {
    type VariableSymbol;
    fn variable(name: Self::VariableSymbol) -> Self;
}

pub trait ConstantHelpers {
    fn bool(value: bool) -> Self;
    fn int(value: i64) -> Self;
}

pub trait UnaryOperationHelpers {
    type UnaryOperationKind;
    fn unary_operation(kind: Self::UnaryOperationKind, arg: Self) -> Self;
    fn not(arg: Self) -> Self;
    fn minus(arg: Self) -> Self;
}

pub trait BinaryOperationHelpers: Sized + UnaryOperationHelpers {
    type BinaryOperationKind;
    fn binary_operation(kind: Self::BinaryOperationKind, left: Self, right: Self) -> Self;
    fn equals(left: Self, right: Self) -> Self;
    fn not_equals(left: Self, right: Self) -> Self;
    fn greater_than(left: Self, right: Self) -> Self;
    fn greater_equals(left: Self, right: Self) -> Self;
    fn less_than(left: Self, right: Self) -> Self;
    fn less_equals(left: Self, right: Self) -> Self;
    fn add(left: Self, right: Self) -> Self;
    fn subtract(left: Self, right: Self) -> Self;
    fn multiply(left: Self, right: Self) -> Self;
    fn divide(left: Self, right: Self) -> Self;
    fn module(left: Self, right: Self) -> Self;
    fn and(left: Self, right: Self) -> Self;
    fn or(left: Self, right: Self) -> Self;
    fn xor(left: Self, right: Self) -> Self {
        Self::not(Self::equals(left, right))
    }
    fn implies(left: Self, right: Self) -> Self;
}

pub fn equals<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::equals(left, right)
}
pub fn not_equals<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::not_equals(left, right)
}
pub fn greater_than<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::greater_than(left, right)
}
pub fn greater_equals<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::greater_equals(left, right)
}
pub fn less_than<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::less_than(left, right)
}
pub fn less_equals<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::less_equals(left, right)
}
pub fn add<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::add(left, right)
}
pub fn subtract<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::subtract(left, right)
}
pub fn multiply<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::multiply(left, right)
}
pub fn divide<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::divide(left, right)
}
pub fn module<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::module(left, right)
}
pub fn and<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::and(left, right)
}
pub fn or<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::or(left, right)
}
pub fn implies<E: BinaryOperationHelpers>(left: E, right: E) -> E {
    BinaryOperationHelpers::implies(left, right)
}

pub trait QuantifierHelpers {
    type QuantifierKind;
    type BoundedVariableDecl;
    type Trigger;
    fn quantifier(
        kind: Self::QuantifierKind,
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self;
    fn forall(
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self;
    fn exists(
        variables: Vec<Self::BoundedVariableDecl>,
        triggers: Vec<Self::Trigger>,
        body: Self,
    ) -> Self;
}

pub trait FunctionApplicationHelpers: Sized {
    type FunctionSymbol;
    fn call(function: Self::FunctionSymbol, args: Vec<Self>) -> Self;
}

pub trait LabelledExpressionHelpers {
    type LabelPositivity;
    type LabelSymbol;
    fn labelled_expression(
        positivity: Self::LabelPositivity,
        name: Self::LabelSymbol,
        expression: Self,
    ) -> Self;
    fn label_negative(name: Self::LabelSymbol, expression: Self) -> Self;
    fn label_positive(name: Self::LabelSymbol, expression: Self) -> Self;
}

pub trait SyntacticEvaluation {
    /// Check whether the expression is syntactically known to be true.
    fn is_true(&self) -> bool;
    /// Check whether the expression is syntactically known to be false.
    fn is_false(&self) -> bool;
}

pub trait ExpressionIterator<E> {
    /// Conjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn conjoin(&mut self) -> E;

    /// Disjoin a sequence of expressions into a single expression.
    /// Returns true if the sequence has no elements.
    fn disjoin(&mut self) -> E;
}

impl<I, E> ExpressionIterator<E> for I
where
    I: Iterator<Item = E>,
    E: BinaryOperationHelpers + ConstantHelpers,
{
    fn conjoin(&mut self) -> E {
        if let Some(mut conjunction) = self.next() {
            for conjunct in self {
                conjunction = E::and(conjunction, conjunct);
            }
            conjunction
        } else {
            E::bool(true)
        }
    }

    fn disjoin(&mut self) -> E {
        if let Some(mut disjunction) = self.next() {
            for disjunct in self {
                disjunction = E::and(disjunction, disjunct);
            }
            disjunction
        } else {
            E::bool(false)
        }
    }
}
