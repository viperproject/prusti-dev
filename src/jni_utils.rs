use jni::JNIEnv;
use jni::objects::JObject;
use jni::errors::Result;
use jni::objects::JString;
use jni::sys::jsize;
use viper_sys::wrappers::*;
use error_chain::ChainedError;

pub struct JniUtils<'a> {
    env: &'a JNIEnv<'a>,
}

impl<'a> JniUtils<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        JniUtils { env }
    }

    pub fn unwrap_result<T>(&self, res: Result<T>) -> T {
        res.unwrap_or_else(|error| {
            let exception_occurred = self.env.exception_check().unwrap_or_else(
                |e| panic!(format!("{:?}", e)),
            );
            if exception_occurred {
                self.env.exception_describe().unwrap_or_else(
                    |e| panic!(format!("{:?}", e)),
                );
            }
            panic!(format!("{}", error.display_chain().to_string()));
        })
    }

    pub fn new_option(&self, opt: Option<JObject>) -> JObject {
        match opt {
            Some(o) => self.unwrap_result(scala::Some::with(self.env).new(o)),
            None => self.unwrap_result(scala::None_object::with(self.env).singleton()),
        }
    }

    pub fn new_string(&self, string: &str) -> JObject {
        self.unwrap_result(self.env.new_string(string)).into()
    }

    pub fn new_seq(&self, objects: Vec<JObject>) -> JObject {
        let array_seq_wrapper = scala::collection::mutable::ArraySeq::with(self.env);
        let len = objects.len();
        let res = self.unwrap_result(array_seq_wrapper.new(len as i32));
        for i in 0..len {
            self.unwrap_result(array_seq_wrapper.call_update(res, i as i32, objects[i]));
        }
        res
    }

    pub fn get_string(&self, string_object: JObject) -> String {
        self.unwrap_result(self.env.get_string(JString::from(string_object)))
            .into()
    }

    pub fn to_string(&self, object: JObject) -> String {
        let object_wrapper = java::lang::Object::with(self.env);
        let string_object = self.unwrap_result(object_wrapper.call_toString(object));
        let java_str = self.get_string(string_object);
        java_str.into()
    }

    pub fn class_name(&self, object: JObject) -> String {
        let class: JObject = self.unwrap_result(self.env.get_object_class(object)).into();
        let class_name_object =
            self.unwrap_result(java::lang::Class::with(self.env).call_getName(class));
        self.get_string(class_name_object)
    }

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

    pub fn is_instance_of(&self, instance: JObject, class: &str) -> bool {
        let instance_class = self.unwrap_result(self.env.get_object_class(instance));
        let super_class = self.unwrap_result(self.env.find_class(class));
        self.unwrap_result(self.env.is_assignable_from(instance_class, super_class))
    }

    pub fn new_object_array(&self, length: jsize) -> JObject {
        let object_class = self.unwrap_result(self.env.find_class("java/lang/Object"));
        JObject::from(self.unwrap_result(self.env.new_object_array(
            length,
            object_class,
            JObject::null(),
        )))
    }

    #[allow(dead_code)]
    pub fn seq_to_array(&self, sequence: JObject, elements_class_ref: &str) -> JObject {
        let elements_class = self.unwrap_result(self.env.find_class(elements_class_ref));
        let class_tag_object_wrapper = scala::reflect::ClassTag_object::with(self.env);
        let class_tag_object = self.unwrap_result(class_tag_object_wrapper.singleton());
        let elements_class_tag = self.unwrap_result(class_tag_object_wrapper.call_apply(
            class_tag_object,
            elements_class.into(),
        ));
        self.unwrap_result(scala::collection::Seq::with(self.env).call_toArray(
            sequence,
            elements_class_tag,
        ))
    }
}
