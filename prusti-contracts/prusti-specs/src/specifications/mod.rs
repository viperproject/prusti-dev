/// The following grammar defines Prusti expressions (this is an LL(finite) grammar):
/// assertion ::= prusti_expr ;
/// pledge ::= pledge_lhs, ",", prusti_expr ;
/// pledge_lhs ::= [ ? actual rust expression ?, "=>" ], prusti_expr ;
/// 
/// prusti_expr ::= conjunction, [ "==>", prusti_expr ] ;
/// conjunction ::= entailment, { "&&", entailment } ;
/// entailment ::= primary | ? actual rust expression ?, [ "|=", [ "|", ? args as parsed by syn2 ?, "|" ], "[", [ ( requires | ensures ), { ",", ( requires | ensures ) } ], "]" ] ;
/// primary ::= "(", prusti_expr, ")"
///           | "forall", "(", "|", ? one or more args as parsed by syn2 ?, "|", prusti_expr, [ ",", "triggers", "=", ? array as parsed by syn2 ? ] ")"
///           ;
/// requires ::= "requires", "(", prusti_expr, ")" ;
/// ensures ::= "ensures", "(", prusti_expr, ")" ;
/// 
/// This grammar doesn't yet handle the unintuitive precedence difference between `&&` and `||` operators.

pub mod common;
pub mod preparser;
pub mod untyped;

pub use common::SpecType;
