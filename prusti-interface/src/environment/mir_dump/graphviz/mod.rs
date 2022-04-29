pub mod to_text;

pub(super) use self::to_text::{
    loan_containment_to_text, loan_to_text, loans_to_text, to_sorted_text,
};

pub use self::to_text::{opaque_lifetime_string, ToText};

pub(super) use vir::common::graphviz::{Graph, NodeBuilder};
