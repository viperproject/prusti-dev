use crate::{
    generate_for_ensures, generate_for_requires, do_generate_for_pure, parse_ghost_constraint, untyped, GeneratedResult,
    NestedSpec,
};
use proc_macro2::TokenStream;
use syn::{parse_quote_spanned, spanned::Spanned};

pub fn generate(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let tokens_span = attr.span();

    // Parse ghost constraint information
    let ghost_constraint = parse_ghost_constraint(attr)?;

    let mut new_items = vec![];
    let mut new_attrs = vec![];

    for nested_spec in ghost_constraint.specs {
        let (mut generated_items, generated_attrs) = match nested_spec {
            NestedSpec::Ensures(tokens) => generate_for_ensures(tokens, item)?,
            NestedSpec::Requires(tokens) => generate_for_requires(tokens, item)?,
            NestedSpec::Pure => do_generate_for_pure(item)?,
        };

        for generated_item in generated_items.iter_mut() {
            let item_fn = match generated_item {
                syn::Item::Fn(item_fn) => item_fn,
                _ => unreachable!(),
            };

            // Add bounds as a where clause
            item_fn.sig.generics.where_clause = Some(generate_where_clause_for_spec(
                &ghost_constraint.trait_bounds,
                item_fn.sig.generics.where_clause.as_ref(),
            ));

            // Add attribute to mark this as a "specification with constraint" (used for processing the contract in `SpecCollector`)
            item_fn.attrs.push(parse_quote_spanned! {tokens_span=>
                #[prusti::ghost_constraint_trait_bounds_in_where_clause]
            });
        }

        new_items.extend(generated_items);
        new_attrs.extend(generated_attrs);
    }

    Ok((new_items, new_attrs))
}

fn generate_where_clause_for_spec(
    trait_bounds: &syn::PredicateType,
    existing_where_clause: Option<&syn::WhereClause>,
) -> syn::WhereClause {
    let span = trait_bounds.span();
    if let Some(mut where_clause) = existing_where_clause.cloned() {
        where_clause.predicates.push(parse_quote_spanned! {span=>
            #trait_bounds
        });
        where_clause
    } else {
        parse_quote_spanned! {span=>
            where #trait_bounds
        }
    }
}
