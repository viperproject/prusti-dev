use jni::objects::JObject;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::JavaVM;
use systest::print_exception;
use systest::wrappers::*;

#[test]
#[should_panic(expected = "Java binding type failure. Expected object of class java/lang/String, but got java/lang/Integer instead")]
fn constructor_should_fail_on_wrong_argument() {
    let jvm_args = InitArgsBuilder::new()
        .version(JNIVersion::V8)
        .option("-Xcheck:jni")
        .option("-Xdebug")
        .option("-XX:+CheckJNICalls")
        //.option("-verbose:jni")
        //.option("-XX:+TraceJNICalls")
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
        let integer_object = java::lang::Integer::with(&env).new(1337)?;
        let error_wrapper = java::lang::Error::with(&env);
        let _result = error_wrapper.new(integer_object);
        Ok(JObject::null())
    }).unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
