extern crate viper_sys;
extern crate jni;
extern crate error_chain;

use error_chain::ChainedError;
use jni::JavaVM;
use jni::InitArgsBuilder;
use jni::JNIVersion;
use jni::objects::JObject;
use jni::objects::JValue;
use viper_sys::print_exception;

#[test]
fn test_jvm_builtin_classes() {
    let jvm_args = InitArgsBuilder::new()
        .version(JNIVersion::V8)
        .option("-verbose:gc")
        .option("-Xcheck:jni")
        .option("-Xdebug")
        .option("-XX:+CheckJNICalls")
        //.option("-Djava.security.debug=all")
        //.option("-verbose:jni")
        //.option("-XX:+TraceJNICalls")
        .build()
        .unwrap_or_else(|e| {
            panic!(format!("{}", e.display_chain().to_string()));
        });

    let jvm = JavaVM::new(jvm_args).unwrap_or_else(|e| {
        panic!(format!("{}", e.display_chain().to_string()));
    });

    let env = jvm.attach_current_thread().expect(
        "failed to attach jvm thread",
    );

    for int_value in -10..10 {
        for array_length in 1..50 {
            env.with_local_frame(16, || {
                let integer_value = JObject::from(env.new_object(
                    "java/lang/Integer",
                    "(I)V",
                    &[JValue::Int(int_value)],
                )?);

                let int_array = JObject::from(env.new_object_array(
                    array_length,
                    "java/lang/Integer",
                    integer_value,
                )?);

                let result = env.call_static_method(
                    "java/util/Arrays",
                    "binarySearch",
                    "([Ljava/lang/Object;Ljava/lang/Object;)I",
                    &[JValue::Object(int_array), JValue::Object(integer_value)],
                )?
                    .i()?;

                assert!(0 <= result && result < array_length);

                Ok(JObject::null())

            }).unwrap_or_else(|e| {
                    print_exception(&env);
                    panic!(format!("{}", e.display_chain().to_string()));
                });
        }
    }
}
