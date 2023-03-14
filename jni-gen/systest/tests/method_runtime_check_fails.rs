use jni::objects::JObject;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::JavaVM;
use jni::JNIEnv;
use jni::errors::Result as JNIResult;
use systest::print_exception;
use systest::wrappers::*;

fn string_to_jobject<'a>(env: &JNIEnv<'a>, string: &str) -> JNIResult<JObject<'a>> {
    Ok(JObject::from(env.new_string(string.to_owned())?))
}

#[test]
#[should_panic(expected = "Java binding type failure. Expected object of class java/lang/String, but got java/lang/Integer instead")]
fn method_should_fail_on_wrong_receiver() {
    let jvm_args = InitArgsBuilder::new()
    .version(JNIVersion::V8)
    .option("-Xcheck:jni")
    .option("-Xdebug")
    .option("-XX:+CheckJNICalls")
    .build()
    .unwrap_or_else(|e| {
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let error_wrapper = java::lang::Error::with(&env);
        let integer_object = java::lang::Integer::with(&env).new(1337)?;
        error_wrapper.call_getMessage(integer_object)?;
        Ok(JObject::null())
    }).unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}

#[test]
#[should_panic(expected = "Java binding type failure. Expected object of class java/lang/Integer, but got java/lang/Error instead")]
fn method_should_fail_on_wrong_argument() {
    let jvm_args = InitArgsBuilder::new()
    .version(JNIVersion::V8)
    .option("-Xcheck:jni")
    .option("-Xdebug")
    .option("-XX:+CheckJNICalls")
    .build()
    .unwrap_or_else(|e| {
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    env.with_local_frame(16, || {
        let integer_wrapper = java::lang::Integer::with(&env);
        let integer_object = integer_wrapper.new(1337)?;
        let error_wrapper = java::lang::Error::with(&env);
        let error_object = error_wrapper.new(string_to_jobject(&env, "error message")?)?;
        let _result = integer_wrapper.call_compareTo(integer_object, error_object);
        Ok(JObject::null())
    }).unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
