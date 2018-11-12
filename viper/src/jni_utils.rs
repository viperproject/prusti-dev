// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use jni::JNIEnv;
use jni::objects::JObject;
use jni::errors::Result;
use jni::objects::JString;
use jni::sys::jsize;
use viper_sys::wrappers::*;
use error_chain::ChainedError;

#[derive(Clone, Copy)]
pub struct JniUtils<'a> {
    env: &'a JNIEnv<'a>,
}

impl<'a> JniUtils<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        JniUtils { env }
    }

    /// Generates the stack trace from a Java Exception
    pub fn get_stack_trace(&self, t: JObject) -> Result<String> {
        let sw = java::io::StringWriter::with(self.env).new()?;
        let pw = java::io::PrintWriter::with(self.env).new(sw)?;
        java::lang::Throwable::with(self.env).call_printStackTrace(t, pw)?;
        Ok(self.to_string(sw))
    }

    /// Unwraps a Result<T>, checking for Java Exceptions.
    pub fn unwrap_result<T>(&self, res: Result<T>) -> T {
        res.unwrap_or_else(|error| {
            error!("{}", error.display_chain().to_string());
            let exception_occurred = self.env.exception_check().unwrap_or_else(|e| {
                error!("{}", e.display_chain().to_string());
                panic!();
            });
            if exception_occurred {
                self.env.exception_describe().unwrap_or_else(|e| {
                    error!("{}", e.display_chain().to_string());
                    panic!();
                });

                /*let throwable = self.env.exception_occurred().unwrap_or_else(|e| {
                    error!("{}", e.display_chain().to_string());
                    panic!();
                });*/

                self.env.exception_clear().unwrap_or_else(|e| {
                    error!("{}", e.display_chain().to_string());
                    panic!();
                });

                /*let stack_trace = self.get_stack_trace(throwable.into()).unwrap_or_else(|e| {
                    error!("{}", e.display_chain().to_string());
                    panic!();
                });
                error!("Exception stack trace:\n{}", stack_trace);*/
            }
            panic!();
        })
    }

    pub fn retry_on_exception<F, T>(&self, f: F, retry: usize) -> T where F: Fn() -> Result<T> {
        let mut res = f();
        for _ in 0..retry {
            if res.is_ok() {
                break;
            } else {
                self.env.exception_clear();
                res = f();
            }
        }
        self.unwrap_result(res)
    }

    /// Converts a Rust Option<JObject> to a Scala Option
    pub fn new_option(&self, opt: Option<JObject>) -> JObject {
        match opt {
            Some(o) => self.unwrap_result(scala::Some::with(self.env).new(o)),
            None => self.unwrap_result(scala::None_object::with(self.env).singleton()),
        }
    }

    /// Converts a Rust String to a Java String
    pub fn new_string(&self, string: &str) -> JObject {
        self.unwrap_result(self.env.new_string(string)).into()
    }

    pub fn new_map(&self, items: &[(JObject, JObject)]) -> JObject {
        let hash_map_wrapper = scala::collection::immutable::HashMap::with(self.env);
        let mut result = self.unwrap_result(hash_map_wrapper.new());
        for &(k, v) in items {
            result = self.unwrap_result(hash_map_wrapper.call_updated(result, k, v));
        }
        result
    }

    /// Converts a Rust number to a Java BigInt
    pub fn new_big_int(&self, number: &ToString) -> JObject {
        let number_string = self.new_string(&number.to_string());

        let java_big_integer =
            self.unwrap_result(java::math::BigInteger::with(self.env).new(number_string));

        self.unwrap_result(scala::math::BigInt::with(self.env).new(java_big_integer))
    }

    /// Converts a Rust Vec<JObject> to a Scala Seq
    pub fn new_seq(&self, objects: &[JObject]) -> JObject {
        let array_seq_wrapper = scala::collection::mutable::ArraySeq::with(self.env);
        let len = objects.len();
        let res = self.unwrap_result(array_seq_wrapper.new(len as i32));
        for (i, obj) in objects.iter().enumerate() {
            self.unwrap_result(array_seq_wrapper.call_update(res, i as i32, *obj));
        }
        res
    }

    /// Converts a Java String to a Rust String
    pub fn get_string(&self, string_object: JObject) -> String {
        self.unwrap_result(self.env.get_string(JString::from(string_object)))
            .into()
    }

    /// Calls the "toString" method on a Java object and returns the result as a Rust String
    pub fn to_string(&self, object: JObject) -> String {
        let object_wrapper = java::lang::Object::with(self.env);
        let string_object = self.unwrap_result(object_wrapper.call_toString(object));
        self.get_string(string_object)
    }

    /// Returns the name of the class of a Java object as Rust String
    pub fn class_name(&self, object: JObject) -> String {
        let class: JObject = self.unwrap_result(self.env.get_object_class(object)).into();
        let class_name_object =
            self.unwrap_result(java::lang::Class::with(self.env).call_getName(class));
        self.get_string(class_name_object)
    }

    /// Convert a Scala Seq to a Rust Vec<JObject>
    pub fn seq_to_vec(&self, sequence: JObject) -> Vec<JObject> {
        let mut res: Vec<JObject> = vec![];
        let seq_wrapper = scala::collection::Seq::with(self.env);
        let length = self.unwrap_result(seq_wrapper.call_length(sequence));
        for i in 0..length {
            let item: JObject = self.unwrap_result(seq_wrapper.call_apply(sequence, i));
            res.push(item);
        }
        res
    }

    /// Checks if an object is a subtype of a Java class
    pub fn is_instance_of(&self, object: JObject, class: &str) -> bool {
        let object_class = self.unwrap_result(self.env.get_object_class(object));
        let super_class = self.unwrap_result(self.env.find_class(class));
        self.unwrap_result(self.env.is_assignable_from(object_class, super_class))
    }

    /// Returns a new Java array of objects, initialised with null values
    pub fn new_object_array(&self, length: jsize) -> JObject {
        let object_class = self.unwrap_result(self.env.find_class("java/lang/Object"));
        JObject::from(self.unwrap_result(self.env.new_object_array(
            length,
            object_class,
            JObject::null(),
        )))
    }

    /// Converts a Scala Seq to a Java Array
    #[allow(dead_code)]
    pub fn seq_to_array(&self, sequence: JObject, elements_class_ref: &str) -> JObject {
        let elements_class = self.unwrap_result(self.env.find_class(elements_class_ref));
        let class_tag_object_wrapper = scala::reflect::ClassTag_object::with(self.env);
        let class_tag_object = self.unwrap_result(class_tag_object_wrapper.singleton());
        let elements_class_tag = self.unwrap_result(
            class_tag_object_wrapper.call_apply(class_tag_object, elements_class.into()),
        );
        self.unwrap_result(
            scala::collection::Seq::with(self.env).call_toArray(sequence, elements_class_tag),
        )
    }
}
