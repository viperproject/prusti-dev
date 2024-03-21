use jni::{objects::JObject, JNIEnv};
use jni::strings::JavaStr;
use std::ffi::CStr;
use jni::errors::Result;

pub fn java_str_to_string(string: &JavaStr) -> Result<String> {
    unsafe { Ok(CStr::from_ptr(string.get_raw()).to_str().unwrap_or_else(|err| panic!("java_str_to_string - failed to convert string: {err:?}")).to_string()) }
}

fn get_jobject_class_name_inner<'a, 'c, O>(env: &'c JNIEnv<'c>, object: O) -> Result<String>
where
    O: Into<JObject<'a>>
{
    let object_class = env.get_object_class(object)?;
    java_str_to_string(
        &env.get_string(
            env.call_method(object_class, "getName", "()Ljava/lang/String;", &[])?
                 .l()?
                 .into(),
        )?,
    )
}

pub fn get_jobject_class_name<'a, O>(env: &'a JNIEnv<'a>, object: O) -> String
where
    O: Into<JObject<'a>>
{
    get_jobject_class_name_inner(env, object).unwrap_or("<unknown>".to_string()).replace('.', "/")
}
