use vir_crate::low::{self as vir_low};

pub(in super::super) enum HeapEntry {
    Comment(vir_low::ast::statement::Comment),
    Label(vir_low::ast::statement::Label),
    /// An inhale entry that can be purified.
    InhalePredicate(
        vir_low::ast::expression::PredicateAccessPredicate,
        vir_low::Position,
    ),
    /// An exhale entry that can be purified.
    ExhalePredicate(
        vir_low::ast::expression::PredicateAccessPredicate,
        vir_low::Position,
    ),
    /// A generic inhale entry that cannot be purified.
    InhaleGeneric(vir_low::ast::statement::Inhale),
    /// A generic exhale entry that cannot be purified.
    ExhaleGeneric(vir_low::ast::statement::Exhale),
    Assume(vir_low::ast::statement::Assume),
    Assert(vir_low::ast::statement::Assert),
}

impl std::fmt::Display for HeapEntry {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            HeapEntry::Comment(statement) => write!(f, "{statement}"),
            HeapEntry::Label(statement) => write!(f, "{statement}"),
            HeapEntry::InhalePredicate(predicate, _position) => {
                write!(f, "inhale-predicate {predicate}")
            }
            HeapEntry::ExhalePredicate(predicate, _position) => {
                write!(f, "exhale-predicate {predicate}")
            }
            HeapEntry::InhaleGeneric(statement) => write!(f, "{statement}"),
            HeapEntry::ExhaleGeneric(statement) => write!(f, "{statement}"),
            HeapEntry::Assume(statement) => write!(f, "{statement}"),
            HeapEntry::Assert(statement) => write!(f, "{statement}"),
        }
    }
}
