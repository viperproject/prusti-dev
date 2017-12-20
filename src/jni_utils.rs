use jni::JNIEnv;
use jni::objects::JObject;
use jni::errors::Result;
use jni::objects::JString;
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

    pub fn to_string(&self, object: JObject) -> String {
        let object_wrapper = java::lang::Object::with(self.env);
        let string_object = self.unwrap_result(object_wrapper.call_toString(object));
        let java_str = self.unwrap_result(self.env.get_string(JString::from(string_object)));
        java_str.into()
    }
}
