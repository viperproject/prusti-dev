// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::ast_factory::{structs::Type, AstFactory};
use jni::objects::JObject;
use viper_sys::wrappers::viper::silver::ast;

impl<'a> AstFactory<'a> {
    pub fn int_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Int_object)
    }

    pub fn bool_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Bool_object)
    }

    pub fn perm_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Perm_object)
    }

    pub fn ref_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Ref_object)
    }

    pub fn wand_type(&self) -> Type<'a> {
        get_ast_object!(self, Type, ast::Wand_object)
    }

    pub fn type_var(&self, name: &str) -> Type<'a> {
        let obj = self
            .jni
            .unwrap_result(ast::TypeVar::with(self.env).new(self.jni.new_string(name)));
        Type::new(obj)
    }

    pub fn domain_type(
        &self,
        domain_name: &str,
        partial_typ_vars_map: &[(Type, Type)],
        type_parameters: &[Type],
    ) -> Type<'a> {
        let obj = self.jni.unwrap_result(
            ast::DomainType::with(self.env).new(
                self.jni.new_string(domain_name),
                self.jni
                    .new_map(&map_to_jobject_pairs!(partial_typ_vars_map)),
                self.jni.new_seq(&map_to_jobjects!(type_parameters)),
            ),
        );
        Type::new(obj)
    }

    pub fn set_type(&self, element_type: Type) -> Type<'a> {
        let obj = self
            .jni
            .unwrap_result(ast::SetType::with(self.env).new(element_type.to_jobject()));
        Type::new(obj)
    }

    pub fn multiset_type(&self, element_type: Type) -> Type<'a> {
        let obj = self
            .jni
            .unwrap_result(ast::MultisetType::with(self.env).new(element_type.to_jobject()));
        Type::new(obj)
    }

    pub fn seq_type(&self, element_type: Type) -> Type<'a> {
        let obj = self
            .jni
            .unwrap_result(ast::SeqType::with(self.env).new(element_type.to_jobject()));
        Type::new(obj)
    }

    pub fn map_type(&self, key_type: Type, val_type: Type) -> Type<'a> {
        let obj = self.jni.unwrap_result(
            ast::MapType::with(self.env).new(key_type.to_jobject(), val_type.to_jobject()),
        );
        Type::new(obj)
    }

    pub fn backend_f32_type(&self) -> Type<'a> {
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap();
        let float_factory_ = ast::utility::FloatFactory::with(self.env);
        let float_factory = ast::utility::FloatFactory::new(&float_factory_, 24, 8, rm).unwrap();

        let obj = self.jni.unwrap_result(ast::utility::FloatFactory::call_typ(
            &float_factory_,
            float_factory,
        ));
        Type::new(obj)
    }

    pub fn backend_f64_type(&self) -> Type<'a> {
        let rm = ast::utility::RoundingMode::with(self.env)
            .call_RNE()
            .unwrap();
        let float_factory_ = ast::utility::FloatFactory::with(self.env);
        let float_factory = ast::utility::FloatFactory::new(&float_factory_, 52, 12, rm).unwrap();

        let obj = self.jni.unwrap_result(ast::utility::FloatFactory::call_typ(
            &float_factory_,
            float_factory,
        ));
        Type::new(obj)
    }

    pub fn backend_bv8_type(&self) -> Type<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 8).unwrap();
        let obj = self
            .jni
            .unwrap_result(ast::utility::BVFactory::call_typ(&bv_factory_, bv_factory));
        Type::new(obj)
    }

    pub fn backend_bv16_type(&self) -> Type<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 16).unwrap();
        let obj = self
            .jni
            .unwrap_result(ast::utility::BVFactory::call_typ(&bv_factory_, bv_factory));
        Type::new(obj)
    }

    pub fn backend_bv32_type(&self) -> Type<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 32).unwrap();
        let obj = self
            .jni
            .unwrap_result(ast::utility::BVFactory::call_typ(&bv_factory_, bv_factory));
        Type::new(obj)
    }

    pub fn backend_bv64_type(&self) -> Type<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 64).unwrap();
        let obj = self
            .jni
            .unwrap_result(ast::utility::BVFactory::call_typ(&bv_factory_, bv_factory));
        Type::new(obj)
    }

    pub fn backend_bv128_type(&self) -> Type<'a> {
        let bv_factory_ = ast::utility::BVFactory::with(self.env);
        let bv_factory = ast::utility::BVFactory::new(&bv_factory_, 128).unwrap();
        let obj = self
            .jni
            .unwrap_result(ast::utility::BVFactory::call_typ(&bv_factory_, bv_factory));
        Type::new(obj)
    }
}
