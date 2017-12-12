use syntax::{self, ast};
use syntax::symbol::Symbol;
use syntax::codemap::Span;

#[derive(Debug)]
pub enum Type {
    Precondition,
    Postcondition,
    Invariant,
}

pub struct Specification {
    pub spec_type: Type,
    pub node_identifier: ast::Ident,
    pub span: Span,
    pub spec_string: String,
    pub spec_expr: syntax::ptr::P<ast::Expr>,
}

pub struct SpecificationManager {
    specs: Vec<Specification>,
}

impl SpecificationManager {

    pub fn new() -> SpecificationManager {
        SpecificationManager {
            specs: Vec::new(),
        }
    }

    pub fn add_specification(&mut self, spec_type: Symbol,
                             node_identifier: ast::Ident, span: Span,
                             spec: String,
                             expr: syntax::ptr::P<ast::Expr>) {
        let spec_type = match spec_type.as_str().as_ref() {
            "requires" => {
                Type::Precondition
            },
            "ensures" => {
                Type::Postcondition
            },
            "invariant" => {
                Type::Invariant
            },
            _ => {
                panic!("Unrecognized specification type: {:?}", spec_type);
            },
        };
        self.specs.push(Specification {
            spec_type: spec_type,
            node_identifier: node_identifier,
            span: span,
            spec_string: spec,
            spec_expr: expr,
        });
    }
}
