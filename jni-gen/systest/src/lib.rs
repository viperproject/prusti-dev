#[path = "../gen/mod.rs"]
pub mod wrappers;

use jni::{errors::Result, objects::JObject, JNIEnv};
use jni_gen::utils::java_str_to_string;

pub fn print_exception(env: &JNIEnv) {
    let exception_occurred = env.exception_check().unwrap_or_else(|e| panic!("{e:?}"));
    if exception_occurred {
        env.exception_describe()
            .unwrap_or_else(|e| panic!("{e:?}"));
    }
}

fn get_jobject_class_name_inner<'a, 'c, O>(env: &'c JNIEnv<'c>, object: O) -> Result<String>
where
    O: Into<JObject<'a>>
{
    let object_class = env.get_object_class(object)?;
    let res = java_str_to_string(
        &env.get_string(
            env.call_method(object_class, "getName", "()Ljava/lang/String;", &[])?
                 .l()?
                 .into(),
        )?,
    );

    match res {
        Ok(str) => Ok(str),
        Err(_) => Ok("Cannot be determined".to_string()),
    }
}

pub fn get_jobject_class_name<'a, O>(env: &'a JNIEnv<'a>, object: O) -> String
where
    O: Into<JObject<'a>>
{
    match get_jobject_class_name_inner(env, object) {
        Ok(result) => result,
        Err(_) => "Cannot be determined".to_string(),
    }
}