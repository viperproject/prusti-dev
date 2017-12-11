use syntax::{self, ast};
use syntax::symbol::Symbol;
use syntax::codemap::Span;

pub enum Type {
    Precondition,
    Postcondition,
    Invariant,
}

pub struct Specification {
    pub spec_type: Type,
    pub string: String,
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
                             name: ast::Ident, span: Span,
                             spec: String,
                             expr: syntax::ptr::P<ast::Expr>) {
        println!("{}({:?}) on {:?}",
            spec_type, expr, name);
        //let mut err = cx.sess().struct_span_err(span, "error");
        //err.emit();
    }
}
