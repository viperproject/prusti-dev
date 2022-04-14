use quote::{quote, ToTokens};

/// Add `PhantomData` markers for each type parameter to silence errors
/// about unused type parameters.
///
/// Given
/// ```text
/// struct Foo<A,B> {
/// }
/// ```
/// Result
/// ```text
/// struct Foo<A,B> {
///     ::core::marker::PhantomData<A>,
///     ::core::marker::PhantomData<B>
/// }
/// ```
pub fn add_phantom_data_for_generic_params(item_struct: &mut syn::ItemStruct) {
    let fields = item_struct.generics.params.iter()
        .flat_map(|param| match param {
            syn::GenericParam::Type(tp) => {
                let ident = tp.ident.clone();
                Some(quote!(::core::marker::PhantomData<#ident>))
            }
            syn::GenericParam::Lifetime(ld) => {
                let ident = ld.lifetime.clone();
                Some(quote!(&#ident ::core::marker::PhantomData<()>))
            }
            syn::GenericParam::Const(_cp) => None,
        });

    item_struct.fields = syn::Fields::Unnamed(syn::parse_quote! { ( #(#fields),* ) });
}

/// We take the Generics (parameters) defined with the `#[extern_spec] impl<...>` (the `<...>`)
/// but then need to pass those as arguments: `SomeStruct<...>`. This function translates from
/// the syntax of one to the other; e.g. `<T: Bound, 'l: Bound, const C: usize>` -> `<T, 'l, C>`
pub fn rewrite_generics(gens: &syn::Generics) -> syn::AngleBracketedGenericArguments {
    let args: Vec<syn::GenericArgument> = gens
        .params
        .clone()
        .into_iter()
        .map(|gp| {
            let ts = match gp {
                syn::GenericParam::Type(syn::TypeParam { ident, .. })
                | syn::GenericParam::Const(syn::ConstParam { ident, .. }) => ident.into_token_stream(),
                syn::GenericParam::Lifetime(ld) => ld.lifetime.into_token_stream(),
            };
            syn::parse2::<syn::GenericArgument>(ts).unwrap()
        })
        .collect();
    syn::parse_quote! { < #(#args),* > }
}
