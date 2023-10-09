use crate::common::HasSignature;
use proc_macro2::Span;
use rustc_hash::FxHashMap;
use syn::{parse_quote_spanned, spanned::Spanned};

/// Information about the function that a specification is attached to
pub(crate) struct AssociatedFunctionInfo {
    /// the arguments of the associated function
    pub inputs: FxHashMap<String, Argument>,
}

impl AssociatedFunctionInfo {
    /// Used for assertions etc., where there is no associated
    /// function
    pub(crate) fn empty() -> Self {
        Self {
            inputs: Default::default(),
        }
    }

    pub(crate) fn new<T: HasSignature + Spanned>(item: &T) -> syn::Result<Self> {
        let inputs: FxHashMap<String, Argument> = item
            .sig()
            .inputs
            .iter()
            .enumerate()
            .map(|(id, el)| -> syn::Result<(String, Argument)> {
                let arg = create_argument(el, id)?;
                Ok((arg.name.clone(), arg))
            })
            .collect::<syn::Result<FxHashMap<String, Argument>>>()?;
        Ok(Self { inputs })
    }

    pub(crate) fn get_mut_arg(&mut self, name: &String) -> Option<&mut Argument> {
        self.inputs.get_mut(name)
    }
}

/// Arguments to a function / i.e. specification. This struct is meant to
/// Keep track of them and collect information about how they are used
/// within specs to correctly store their old values for runtime checks.
#[derive(Debug)]
pub struct Argument {
    /// name of the argument (stays the same from original function to checks)
    pub name: String,
    /// the type of this argument. If it's none, then only because this is a Self
    /// type.
    pub ty: syn::Type,
    /// whether this value occurrs in an old expression. Don't want to clone
    /// all args, since then they have to implement clone() and the type
    /// resulting from cloning them must be known at ast level
    pub used_in_old: bool,
    /// field in old-tuple (old_values.X) where this argument will be stored
    pub index: usize,
    /// whether or not this field is a reference. We assume that all ref types
    /// start with & (which obviously can be wrong)
    pub is_ref: bool,
    pub is_mutable: bool,
    pub span: Span,
}

pub(crate) fn create_argument(arg: &syn::FnArg, index: usize) -> syn::Result<Argument> {
    let span = arg.span();
    match arg {
        syn::FnArg::Typed(syn::PatType { pat, ty, .. }) => {
            if let syn::Pat::Ident(pat_ident) = *pat.clone() {
                let mut is_mutable = pat_ident.mutability.is_some();

                let is_ref = if let box syn::Type::Reference(ty_ref) = ty {
                    is_mutable = is_mutable || ty_ref.mutability.is_some();
                    true
                } else {
                    false
                };
                let arg = Argument {
                    name: pat_ident.ident.to_string(),
                    ty: *ty.clone(),
                    used_in_old: false,
                    index,
                    is_ref,
                    is_mutable,
                    span,
                };
                Ok(arg)
            } else {
                syn::Result::Err(syn::Error::new(
                    span,
                    "For runtime checks, arguments have to be resolved to identifiers.",
                ))
            }
        }
        syn::FnArg::Receiver(syn::Receiver {
            reference,
            mutability,
            ..
        }) => {
            let is_ref = reference.is_some();
            let is_mutable = mutability.is_some();
            let ty: syn::Type = if is_ref {
                parse_quote_spanned! {span => &Self}
            } else {
                parse_quote_spanned! {span => Self}
            };
            let arg = Argument {
                name: "self".to_string(),
                ty,
                used_in_old: false,
                index,
                is_ref,
                is_mutable,
                span,
            };
            Ok(arg)
        }
    }
}
