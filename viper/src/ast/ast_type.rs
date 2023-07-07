// © 2023, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::jar::{
    viper::silver::ast::{self, Type},
    scala::collection::immutable::{Seq, Map},
};
use duchess::{IntoJava, JavaConstructor, JavaField};
use duchess::java::lang::String as JavaString;

pub fn int_type() -> impl JavaField<Type> {
    ast::Int__::get_module()
}

pub fn bool_type() -> impl JavaField<Type> {
    ast::Bool__::get_module()
}

pub fn perm_type() -> impl JavaField<Type> {
    ast::Perm__::get_module()
}

pub fn ref_type() -> impl JavaField<Type> {
    ast::Ref__::get_module()
}

pub fn wand_type() -> impl JavaField<Type> {
    ast::Wand__::get_module()
}

pub fn type_var(name: impl IntoJava<JavaString>) -> impl JavaConstructor<Type> {
    let typ = ast::TypeVar::new(name);
    Type::new(typ)
}

pub fn domain_type(
    domain_name: impl IntoJava<JavaString>,
    partial_typ_vars_map: impl IntoJava<Map<Type, Type>>,
    type_parameters: impl IntoJava<Seq<Type>>,
) -> impl JavaConstructor<Type> {
    let typ = ast::DomainType::new(domain_name, partial_typ_vars_map, type_parameters);
    Type::new(typ)
}

pub fn set_type(element_type: Type) -> impl JavaConstructor<Type> {
    let typ = ast::SetType::new(element_type);
    Type::new(typ)
}

pub fn multiset_type(element_type: Type) -> impl JavaConstructor<Type> {
    let typ = ast::MultisetType::new(element_type);
    Type::new(typ)
}

pub fn seq_type(element_type: Type) -> impl JavaConstructor<Type> {
    let typ = ast::SeqType::new(element_type);
    Type::new(typ)
}

pub fn map_type(key_type: Type, val_type: Type) -> impl JavaConstructor<Type> {
    let typ = ast::MapType::new(key_type, val_type);
    Type::new(typ)
}

pub fn backend_f32_type() -> impl JavaConstructor<Type> {
    let rm = ast::utility::RoundingMode::RNE();
    let float_factory = ast::utility::FloatFactory::new(24, 8, rm);
    let typ = float_factory.typ();
    Type::new(typ)
}

pub fn backend_f64_type() -> impl JavaConstructor<Type> {
    let rm = ast::utility::RoundingMode::RNE();
    let float_factory = ast::utility::FloatFactory::new(52, 12, rm);
    let typ = float_factory.typ();
    Type::new(typ)
}

pub fn backend_bv8_type() -> impl JavaConstructor<Type> {
    let bv_factory = ast::utility::BVFactory::new(8);
    let typ = bv_factory.typ();
    Type::new(typ)
}

pub fn backend_bv16_type() -> impl JavaConstructor<Type> {
    let bv_factory = ast::utility::BVFactory::new(16);
    let typ = bv_factory.typ();
    Type::new(typ)
}

pub fn backend_bv32_type() -> impl JavaConstructor<Type> {
    let bv_factory = ast::utility::BVFactory::new(32);
    let typ = bv_factory.typ();
    Type::new(typ)
}

pub fn backend_bv64_type() -> impl JavaConstructor<Type> {
    let bv_factory = ast::utility::BVFactory::new(64);
    let typ = bv_factory.typ();
    Type::new(typ)
}

pub fn backend_bv128_type() -> impl JavaConstructor<Type> {
    let bv_factory = ast::utility::BVFactory::new(128);
    let typ = bv_factory.typ();
    Type::new(typ)
}
