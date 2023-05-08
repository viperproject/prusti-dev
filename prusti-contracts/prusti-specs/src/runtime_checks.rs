use proc_macro2::{TokenStream};
use quote::{quote, ToTokens};
use std::str::FromStr;
use syn::{Expr, ExprIf, visit_mut::VisitMut, Path,
        parse::Parse, ExprField};

struct CheckTranslator {
    old_expressions: Vec<Expr>,
}

pub fn translate_check(tokens: TokenStream) -> TokenStream {
    // this unwrap can not really failed since these tokens are parsed before
    // and discarded in prusti_parse
    println!("OUTPUT IS SHOWN\n\n\n\n");
    let mut expr = syn::parse2::<Expr>(tokens).unwrap();
    // let mut visitor = CheckTranslator::new();
    // visitor.visit_expr_mut(&mut expr);

    // after translation:
    // check if expr can be used without translating
    if true {
        quote! {
            assert!(#expr);
        }
    } else {
        expr.to_token_stream()
    }
}

impl CheckTranslator {
    pub fn new() -> Self {
        Self {
            old_expressions: Vec::new(),
        }
    }
}

impl VisitMut for CheckTranslator {
    fn visit_expr_mut(&mut self, expr: &mut syn::Expr) {
        syn::visit_mut::visit_expr_mut(self, expr);

        match expr {
            x@Expr::Call(_) => {
                // check if this expression is "old"
                if let Some(old_arg) = old_contents(x) {
                    // get the one argument
                    // assert!(callexpr.args.len() == 1);
                    self.old_expressions.push(old_arg);
                    // replace old_expression with stored name:
                    let field_name = format!("old_arg.old_{}", self.old_expressions.len());
                    *x = syn::parse2::<Expr>(
                        TokenStream::from_str(&field_name).unwrap()
                    ).unwrap();
                    println!("new x: {:?}", x);

                }
            },
            _ => {}
        }
    }
}

// in the future, this should probably be a bit more sophisticated..
fn old_contents(expr: &mut syn::Expr) -> Option<Expr> {
    if let Expr::Call(call) = expr {
        match *call.func.clone() {
            Expr::Path(syn::ExprPath {path, ..}) => {
                let name = format!("{}", path.segments[0].ident);
                println!("Found function with name: {}", name);
                if name == "old".to_string() {
                    assert!(call.args.len() == 1);
                    Some(call.args[0].clone())
                } else {
                    None
                }
            }
            _ => None
        }
    } else {
        None
    }
}


// problems at the moment:
// - need to figure out all the types of old-expressions! This might be hard..
// - need to create struct containing all the old values, return it from
//   pre-check item, and then pass it to check-function.
// - also need to figure out the pre-condition of pure function calls...
