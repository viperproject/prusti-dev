use crate::{
    generate_for_ensures, generate_for_requires, parse_ghost_constraint, untyped, GeneratedResult,
    NestedSpec,
};
use proc_macro2::TokenStream;
use quote::ToTokens;
use syn::{parse::ParseStream, spanned::Spanned};

pub fn generate(attr: TokenStream, item: &untyped::AnyFnItem) -> GeneratedResult {
    let tokens_span = attr.span();

    // Parse ghost constraint information
    let (trait_bounds_ts, nested_specs) = parse_ghost_constraint(attr)?;
    let trait_bounds: ProvidedTraitBounds = syn::parse2(trait_bounds_ts).map_err(|err|
        syn::Error::new(err.span(), "Could not parse trait bounds")
    )?;

    verify_provided_trait_bounds(&trait_bounds)?;

    let mut new_items = vec![];
    let mut new_attrs = vec![];

    for nested_spec in nested_specs {
        let (mut generated_items, generated_attrs) = match nested_spec {
            NestedSpec::Ensures(tokens) => generate_for_ensures(tokens, item)?,
            NestedSpec::Requires(tokens) => generate_for_requires(tokens, item)?,
        };

        for generated_item in generated_items.iter_mut() {
            let item_fn = match generated_item {
                syn::Item::Fn(item_fn) => item_fn,
                _ => unreachable!(),
            };

            // Add bounds as a where clause
            item_fn.sig.generics.where_clause = Some(generate_where_clause_for_spec(
                &trait_bounds,
                item_fn.sig.generics.where_clause.as_ref(),
            ));

            // Add attribute to mark this as a "specification with constraint" (used for processing the contract in `SpecCollector`)
            item_fn.attrs.push(parse_quote_spanned!(tokens_span=>
                #[prusti::ghost_constraint_trait_bounds_in_where_clause]
            ));
        }

        new_items.extend(generated_items);
        new_attrs.extend(generated_attrs);
    }

    Ok((new_items, new_attrs))
}

fn generate_where_clause_for_spec(
    trait_bounds: &ProvidedTraitBounds,
    preliminary_where_clause: Option<&syn::WhereClause>,
) -> syn::WhereClause {
    let span = trait_bounds.span();
    if let Some(mut where_clause) = preliminary_where_clause.cloned() {
        where_clause.predicates.push(parse_quote_spanned!(span=>
            #trait_bounds
        ));
        where_clause
    } else {
        parse_quote_spanned!(span=>
            where #trait_bounds
        )
    }
}

fn verify_provided_trait_bounds(trait_bounds: &ProvidedTraitBounds) -> syn::Result<()> {
    for bound in &trait_bounds.predicate_type.bounds {
        match bound {
            syn::TypeParamBound::Lifetime(lt) => {
                return Err(syn::Error::new(
                    lt.span(),
                    "Lifetimes in ghost constraints not allowed",
                ))
            }
            syn::TypeParamBound::Trait(trait_bound) => {
                verify_provided_trait_bound(trait_bound)?;
            }
        }
    }

    Ok(())
}

fn verify_provided_trait_bound(trait_bound: &syn::TraitBound) -> syn::Result<()> {
    if let Some(lt) = &trait_bound.lifetimes {
        return Err(syn::Error::new(
            lt.span(),
            "Lifetimes in ghost constraints not allowed",
        ));
    }

    for path_segment in &trait_bound.path.segments {
        match &path_segment.arguments {
            syn::PathArguments::None => (),
            syn::PathArguments::AngleBracketed(angle_bracketed_args) => {
                for generic_arg in &angle_bracketed_args.args {
                    match generic_arg {
                        syn::GenericArgument::Type(_) => (),
                        _ => {
                            return Err(syn::Error::new(
                                generic_arg.span(),
                                "Trait bounds can only have type bindings",
                            ))
                        }
                    }
                }
            }
            _ => unreachable!(), // This should already cause problems in `PrustiTokenStream`
        }
    }

    Ok(())
}

/// A `syn::Parse`able representaiton of `syn::PredicateType` (ignoring bound lifetimes)
struct ProvidedTraitBounds {
    predicate_type: syn::PredicateType,
}

impl syn::parse::Parse for ProvidedTraitBounds {
    fn parse(input: ParseStream) -> syn::Result<Self> {
        Ok(ProvidedTraitBounds {
            predicate_type: syn::PredicateType {
                lifetimes: None,
                bounded_ty: input.parse()?,
                colon_token: input.parse()?,
                bounds: {
                    let mut bounds = syn::punctuated::Punctuated::new();

                    loop {
                        if input.is_empty() {
                            break;
                        }

                        let value = input.parse()?;
                        bounds.push_value(value);

                        if !input.peek(syn::Token![+]) {
                            break;
                        }

                        let punct = input.parse()?;
                        bounds.push_punct(punct);
                    }

                    bounds
                },
            },
        })
    }
}

impl ToTokens for ProvidedTraitBounds {
    fn to_tokens(&self, tokens: &mut TokenStream) {
        self.predicate_type.to_tokens(tokens);
    }
}
