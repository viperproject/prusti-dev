// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashMap,HashSet};
use std::hash::{Hash,Hasher};
use std::iter::Iterator;
use syntax::ast;
use syntax::ext::quote::rt::Span;
use syntax::symbol::Symbol;
use syntax_pos::DUMMY_SP;
use specifications::{SpecID,UntypedSpecification};

// Handles mapping from type to trait declarations it implements.
// Handles trait implementation specID caching

/// This register has several responsibilities:
///
/// 1. During the first parser pass, it registers all:
///    - `struct` declarations,
///    - `impl` blocks,
///    - `trait` declarations.
///    This can then be used during the second parser pass to create the required `impl` blocks on
///    every type implementing the typechecked specification for each trait invariant.
/// 2. During the second parser pass, it allows the querying of trait invariants (see 1.).
/// 3. During the second parser pass, it allows the caching of trait SpecIDs in order to properly
///    register an implementation to a specification ID.
pub struct TraitRegister {
    trait_to_specid: HashMap<RegisterID, SpecID>,
    type_to_trait: HashMap<RegisterID, HashSet<(RegisterID,ast::Item)>>,
    trait_to_inv: HashMap<RegisterID, Vec<ast::Attribute>>,
    func_ref_to_spec: HashMap<FunctionRef, HashMap<RegisterID, Vec<UntypedSpecification>>>,
}

type TraitInfo = (RegisterID, Option<SpecID>, ast::Item, Vec<ast::Attribute>);
pub type FunctionRef = (Symbol, Symbol);

impl TraitRegister {
    pub fn new() -> Self {
        Self { 
            trait_to_specid: HashMap::new(),
            type_to_trait: HashMap::new(),
            trait_to_inv: HashMap::new(),
            func_ref_to_spec: HashMap::new(),
        }
    }

    /// Get all relevant traits for some type item.
    pub fn get_relevant_traits(&self, typ: &ast::Item) -> Vec<TraitInfo> {
        let type_id = RegisterID::from_item(typ);
        if let Some(traits) = self.type_to_trait.get(&type_id) {
            traits.clone().into_iter().map(|(t, impl_item)| {
                let specid_opt = self.trait_to_specid.get(&t).cloned();
                let attrs = self.trait_to_inv.get(&t).cloned().unwrap_or(Vec::new());
                (t, specid_opt, impl_item, attrs)
            }).collect()
        } else {
            Vec::new()
        }
    }

    /// Get span of trait item.
    pub fn get_trait_span(&self, reg_id: &RegisterID) -> Option<Span> {
        let key_val_opt = self.trait_to_inv.get_key_value(&reg_id);
        key_val_opt.map(|(k, _)| k.span.clone())
    }

    /// Get all specifications for some function reference.
    pub fn get_specs(&self, func_ref: &FunctionRef) -> Vec<UntypedSpecification> {
        self.func_ref_to_spec.get(func_ref).map_or(Vec::new(), |map| {
            map
                .values()
                .cloned()
                .flatten()
                .collect()
        })
    }

    /// Registers a SpecID for a trait with RegisterID.
    pub fn register_specid(&mut self, reg_id: RegisterID, specid: SpecID) {
        if self.trait_to_specid.insert(reg_id, specid).is_some() {
            warn!("registering specid to existing trait");
        }
    }

    /// Check if a trait's SpecID is already registered.
    pub fn is_trait_specid_registered(&self, item: &ast::Item) -> bool {
        let trait_id = RegisterID::from_item(item);
        self.trait_to_specid.contains_key(&trait_id)
    }

    /// Register struct declaration and return the ID of the registered item.
    pub fn register_struct(&mut self, item: &ast::Item) -> RegisterID {
        let type_id = RegisterID::from_item(item);
        if !self.type_to_trait.contains_key(&type_id) {
            self.type_to_trait.insert(type_id.clone(), HashSet::new());
        }
        type_id
    }

    /// Returns the internal ID used to represent the item.
    pub fn get_id(&self, item: &ast::Item) -> RegisterID {
        RegisterID::from_item(item)
    }

    /// Register trait declaration and return the ID of the registered item.
    pub fn register_trait_decl(&mut self, item: &ast::Item, specs: &Vec<UntypedSpecification>) -> RegisterID {
        let trait_id = RegisterID::from_item(item);
        self.trait_to_inv.insert(trait_id.clone(), item.attrs.clone());

        let refines = specs
            .iter()
            .filter(|s| s.typ.is_refines())
            .filter(|s| s.typ.get_function_ref().is_some());

        for spec in refines {
            let func_ref = spec.typ.get_function_ref().unwrap();
            if !self.func_ref_to_spec.contains_key(&func_ref) {
                self.func_ref_to_spec.insert(func_ref.clone(), HashMap::new());
            }
            let trait_to_spec_ref = self.func_ref_to_spec.get_mut(&func_ref).unwrap();
            if !trait_to_spec_ref.contains_key(&trait_id) {
                trait_to_spec_ref.insert(trait_id.clone(), Vec::new());
            }
            trait_to_spec_ref.get_mut(&trait_id).unwrap().push(spec.clone());
        }

        trait_id
    }

    /// Register an implementation item.
    pub fn register_impl(&mut self, item: &ast::Item) {
        if let ast::ItemKind::Impl(_, _, _, _, trait_ref_opt, ty, _) = item.node.clone() {
            if trait_ref_opt.is_none() { return ; }
            let trait_decl_id = trait_ref_opt.unwrap().path.into();
            let type_id = match ty.node.clone() {
                ast::TyKind::Path(_, path) => path.into(),
                ast::TyKind::Rptr(_, muty) => if let ast::TyKind::Path(_, path) = muty.ty.node.clone() {
                    path.into()
                } else {
                    warn!("type not supported");
                    RegisterID::dummy()
                },
                _ => {
                    warn!("type not supported");
                    RegisterID::dummy()
                }
            };

            if !self.type_to_trait.contains_key(&type_id) {
                self.type_to_trait.insert(type_id.clone(), HashSet::new());
            }
            self.type_to_trait.get_mut(&type_id).unwrap().insert((trait_decl_id, item.clone()));
        } else {
            warn!("registering item that is not an implementation");
        }
    }
}

#[derive(Eq,Debug,Clone)]
pub struct RegisterID {
    segments: Vec<ast::PathSegment>,
    span: Span,
}

impl RegisterID {
    fn from_item(item: &ast::Item) -> Self {
        ast::Path::from_ident(item.ident).into()
    }

    fn dummy() -> Self {
        Self {
            segments: Vec::new(),
            span: DUMMY_SP,
        }
    }

    #[allow(dead_code)]
    fn is_dummy(&self) -> bool {
        self.segments.is_empty()
    }
}

impl Hash for RegisterID {
    fn hash<H: Hasher>(&self, state: &mut H) {
        // do not hash generic parameters
        self.segments.iter().for_each(|seg| seg.ident.hash(state));
    }
}

impl PartialEq<RegisterID> for RegisterID {
    fn eq(&self, other: &RegisterID) -> bool {
        self.segments.iter().zip(other.segments.iter()).all(|(s,o)| s.ident == o.ident)
    }
}

impl PartialEq<ast::Path> for RegisterID {
    fn eq(&self, other: &ast::Path) -> bool {
        self.segments.iter().zip(other.segments.iter()).all(|(s,o)| s.ident == o.ident)
    }
}

impl From<ast::Path> for RegisterID {
    fn from(path: ast::Path) -> Self {
        Self {
            segments: path.segments,
            span: path.span,
        }
    }
}

impl Into<ast::Path> for RegisterID {
    fn into(self) -> ast::Path {
        ast::Path {
            span: self.span,
            segments: self.segments,
        }
    }
}

impl ToString for RegisterID {
    fn to_string(&self) -> String {
        let components: Vec<String> = self.segments.iter().map(|seg| seg.ident.as_str().to_string()).collect();
        components.join("_")
    }
}
