// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::{
    class_name::*,
    errors::*,
    generators::{
        constructor::*, field_getter_setter::*, method::*, scala_object_getter::*,
        trait_field_getter_setter::*,
    },
    wrapper_spec::*,
};
use jni::JNIEnv;
use log::warn;

pub struct ClassGenerator<'a> {
    env: &'a JNIEnv<'a>,
    class: ClassName,
    items: Vec<ItemWrapperSpec>,
}

impl<'a> ClassGenerator<'a> {
    pub fn new(env: &'a JNIEnv<'a>, class: ClassName, items: Vec<ItemWrapperSpec>) -> Self {
        ClassGenerator { env, class, items }
    }

    fn check(&self) -> Result<()> {
        self.env
            .find_class(self.class.path())
            .map(|_| ())
            .chain_err(|| ErrorKind::NoClass(self.class.full_name()))
    }

    pub fn generate(&self) -> Result<String> {
        self.check()?;

        let mut code: Vec<String> = vec![];
        code.push(format!(
            "//! Automatically generated code for '{}'\n",
            self.class.full_name()
        ));
        code.push("#![allow(dead_code)]\n".to_string());
        code.push("#![allow(non_snake_case)]\n".to_string());
        code.push("#![allow(unused_imports)]\n".to_string());
        code.push("#![allow(clippy::new_ret_no_self)]\n".to_string());
        code.push("#![allow(clippy::wrong_self_convention)]\n".to_string());
        code.push("#![allow(clippy::too_many_arguments)]\n".to_string());
        code.push(self.generate_imports());
        code.push(self.generate_struct());
        code.push(self.generate_begin_impl());
        code.push(self.generate_items()?);
        code.push(self.generate_end_impl());

        Ok(code.join("\n") + "\n")
    }

    fn generate_imports(&self) -> String {
        vec![
            "use jni::JNIEnv;",
            "use jni::objects::GlobalRef;",
            "use jni::objects::JObject;",
            "use jni::objects::JMethodID;",
            "use jni::objects::JStaticFieldID;",
            "use jni::objects::JStaticMethodID;",
            "use jni::objects::JValue;",
            "use jni::objects::JClass;",
            "use jni::errors::Result as JNIResult;",
            "use jni::sys::*;",
            "use jni::signature::*;",
            "use once_cell::sync::OnceCell;",
            "use std::str::FromStr;",
            "use super::builtins::*;",
        ]
        .join("\n")
            + "\n"
    }

    fn generate_struct(&self) -> String {
        let mut code: Vec<String> = vec![];
        code.push("#[allow(non_camel_case_types)]".to_string());
        code.push(format!("pub struct {}<'a> {{", self.class.rust_name()));
        code.push("    env: &'a JNIEnv<'a>,".to_string());
        code.push("}".to_string());

        code.join("\n")
    }

    fn generate_begin_impl(&self) -> String {
        let mut code: Vec<String> = vec![];
        code.push(format!("impl<'a> {}<'a> {{", self.class.rust_name()));
        code.push("".to_string());
        code.push("pub fn with(env: &'a JNIEnv<'a>) -> Self {".to_string());
        code.push(format!("    {}{{ env }}", self.class.rust_name()));
        code.push("}".to_string());
        code.push("".to_string());

        code.join("\n")
    }

    fn generate_end_impl(&self) -> String {
        format!("}} // end of impl {}\n", self.class.rust_name())
    }

    fn generate_items(&self) -> Result<String> {
        let mut gen_items: Vec<String> = vec![];

        if self.items.is_empty() {
            warn!("Class {} does not wrap any item", self.class.full_name())
        }

        for item in &self.items {
            let gen = match *item {
                ItemWrapperSpec::ScalaObjectGetter() => {
                    generate_scala_object_getter(self.env, &self.class)?
                }
                ItemWrapperSpec::Constructor {
                    ref signature,
                    ref suffix,
                } => {
                    generate_constructor(self.env, &self.class, signature.clone(), suffix.clone())?
                }
                ItemWrapperSpec::Method {
                    ref name,
                    ref signature,
                    ref suffix,
                } => generate_method(
                    self.env,
                    &self.class,
                    name,
                    signature.clone(),
                    suffix.clone(),
                )?,
                ItemWrapperSpec::FieldGetterSetter { ref field_name } => {
                    generate_field_getter_setter_for_class(self.env, &self.class, field_name)?
                }
                ItemWrapperSpec::TraitFieldGetterSetter { ref field_name } => {
                    generate_field_getter_setter_for_trait(self.env, &self.class, field_name)?
                }
            };
            gen_items.push(gen)
        }
        Ok(gen_items.join("\n") + "\n")
    }
}
