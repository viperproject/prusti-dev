use jni::objects::JObject;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::JavaVM;
use systest::print_exception;
use systest::wrappers::*;

#[test]
fn test_jvm_builtin_classes() {
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

    for int_value in -10..10 {
        for array_length in 1..50 {
            env.with_local_frame(16, || {
                let integer_value = java::lang::Integer::with(&env).new(int_value)?;

                let int_array = JObject::from(env.new_object_array(
                    array_length,
                    "java/lang/Integer",
                    integer_value,
                )?);

                let result =
                    java::util::Arrays::with(&env).call_binarySearch(int_array, integer_value)?;

                assert!(0 <= result && result < array_length);

                Ok(JObject::null())
            })
            .unwrap_or_else(|e| {
                print_exception(&env);
                panic!("{} source: {:?}", e, std::error::Error::source(&e));
            });
        }
    }
}
