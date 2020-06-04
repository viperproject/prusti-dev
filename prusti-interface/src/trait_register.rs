// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use std::collections::{HashSet,HashMap};
use std::iter::{FromIterator,Iterator};
use syntax::{ast, ptr};


/// Identifier used to store traits and types. Nothing can be done with this type except compare it
/// to other identifers of the same type.
#[derive(Hash, Debug, PartialEq, Eq, Clone)]
pub struct TypePath {
    segments: Vec<ast::PathSegment>,
    // TODO(@jakob): add information about generics
}

impl TypePath {
    fn dummy() -> Self {
        TypePath { segments: Vec::new() }
    }

    #[allow(dead_code)]
    fn is_dummy(&self) -> bool {
        self.segments.is_empty()
    }
}

impl PartialEq<ast::Path> for TypePath {
    fn eq(&self, other: &ast::Path) -> bool {
        self.segments == other.segments
    }
}

impl From<ast::Path> for TypePath {
    fn from(path: ast::Path) -> Self {
        TypePath { segments: path.segments }
    }
}

/// Register containing information on what traits are declared, and what traits are implemented on
/// what types. The register does not consider cross-crate trait implementations, but does consider
/// cross-module implementations.
#[derive(Debug)]
pub struct TraitRegister {
    trait_to_invs: HashMap<TypePath,HashSet<ast::Attribute>>,
    type_to_trait: HashMap<TypePath,HashSet<TypePath>>,
}

impl TraitRegister {
    pub fn new() -> Self {
        TraitRegister {
            trait_to_invs: HashMap::new(),
            type_to_trait: HashMap::new(),
        }
    }

    /// Returns all types registered. This includes types found in declarations and
    /// implementations.
    pub fn types(&self) -> impl Iterator<Item=&TypePath> {
        let hashset: HashSet<_> = self.type_to_trait.keys().collect();
        hashset.into_iter()
    }

    /// Returns all traits the were registered as a declaration.
    pub fn declared_traits(&self) -> impl Iterator<Item=&TypePath> {
        let hashset: HashSet<_> = self.trait_to_invs.keys().collect();
        hashset.into_iter()
    }

    /// Returns all traits registered in an implementation.
    pub fn implemented_traits(&self) -> impl Iterator<Item=&TypePath> {
        let hashset: HashSet<_> = self.type_to_trait.values().flatten().collect();
        hashset.into_iter()
    }

    /// Returns the attributes for some trait. If the trait was not registered, this returns an
    /// empty iterator. This function works on `TypePath`, hence one can provide the converted
    /// `ast::Path` for both the trait implementation  or the trait declaration (up to generics).
    pub fn declaration_attrs(&self, typ: &TypePath) -> impl Iterator<Item=ast::Attribute> {
        if let Some(attrs) = self.trait_to_invs.get(typ).cloned() {
            attrs.into_iter()
        } else {
            HashSet::new().into_iter()
        }
    }

    /// Returns all attributes inherited via trait implementations for some type. Returns an empty
    /// iterator if the type was not registered.
    pub fn inherited_attrs(&self, typ: &TypePath) -> impl Iterator<Item=ast::Attribute> {
        if let Some(traits) = self.type_to_trait.get(typ) {
            traits.iter().flat_map(|t| {
                self.trait_to_invs.get(t).cloned().unwrap_or(HashSet::new())
            }).collect::<HashSet<_>>().into_iter()
        } else {
            HashSet::new().into_iter()
        }
    }

    /// Register a struct declaration.
    pub fn register_struct(&mut self, item: &ptr::P<ast::Item>) {
        // TODO(@jakob): register generics
        let type_name = ast::Path::from_ident(item.ident).into();
        if !self.type_to_trait.contains_key(&type_name) {
            self.type_to_trait.insert(type_name.clone(), HashSet::new());
        }
    }

    /// Register a trait declaration.
    pub fn register_trait_decl(&mut self, item: &ptr::P<ast::Item>) {
        let attrs = HashSet::from_iter(item.attrs.clone().into_iter());
        let trait_name = ast::Path::from_ident(item.ident).into();
        self.trait_to_invs.insert(trait_name, attrs);
    }

    /// Register an implementation block (inherent or trait).
    pub fn register_impl(&mut self, item: &ptr::P<ast::Item>) {
        // FIXME(@jakob): consider generics
        // TODO(@jakob): improve error reporting
        if let ast::ItemKind::Impl(_, _, _, _, trait_ref, ty, _) = item.node.clone() {
            // don't register regular implementations
            if trait_ref.is_none() { return; }
            let trait_name = trait_ref.unwrap().path.clone().into();
            let type_name = match ty.node.clone() {
                ast::TyKind::Path(_, path) => path.into(),
                ast::TyKind::Rptr(_, muty) => if let ast::TyKind::Path(_, path) = muty.ty.node.clone() {
                    path.into()
                } else {
                    warn!("type not supported: {:?}", muty.ty.node);
                    TypePath::dummy()
                },
                _ => {
                    warn!("type not supported: {:?}", ty.node);
                    TypePath::dummy()
                },
            };
            if !self.type_to_trait.contains_key(&type_name) {
                self.type_to_trait.insert(type_name.clone(), HashSet::new());
            }
            self.type_to_trait.get_mut(&type_name).unwrap().insert(trait_name);
        } else {
            warn!("registering item that is not an implementation");
        }
    }

    // register enum declaration

    // register derive?
}

