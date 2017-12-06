extern crate viper_sys;
extern crate jni;
extern crate error_chain;

use error_chain::ChainedError;
use jni::JNIEnv;
use jni::objects::JObject;
use jni::objects::JValue::{Int, Object};
use viper_sys::jvm::*;

#[test]
fn test_jvm_builtin_classes() {
    let jvm_options = [
        //"-Djava.security.debug=all",
        "-verbose:gc",
        //"-verbose:jni",
        "-Xcheck:jni",
        "-Xdebug",
        "-XX:+CheckJNICalls",
        //"-XX:+TraceJNICalls",
    ];

    let (_, raw_jvm_env) = unsafe { build_jvm(&jvm_options) };

    let env: JNIEnv = unsafe { JNIEnv::from_raw(raw_jvm_env).ok().unwrap() };

    for int_value in -10..10 {
        for array_length in 1..50 {
            // TODO: why this works even with 0 capacity?
            env.push_local_frame(0).unwrap_or_else(|e| {
                print_exception(&env);
                println!("{}", e.display_chain().to_string());
                panic!();
            });

            let integer_value = env.new_object("java/lang/Integer", "(I)V", &[Int(int_value)])
                .map(|x| JObject::from(x))
                .and_then(|x| env.new_global_ref(x))
                .unwrap_or_else(|e| {
                    print_exception(&env);
                    println!("{}", e.display_chain().to_string());
                    panic!();
                });

            let int_array =
                env.new_object_array(array_length, "java/lang/Integer", integer_value.as_obj())
                    .map(|x| JObject::from(x))
                    .and_then(|x| env.new_global_ref(x))
                    .unwrap_or_else(|e| {
                        print_exception(&env);
                        println!("{}", e.display_chain().to_string());
                        panic!();
                    });

            let result = env.call_static_method(
                "java/util/Arrays",
                "binarySearch",
                "([Ljava/lang/Object;Ljava/lang/Object;)I",
                &[Object(int_array.as_obj()), Object(integer_value.as_obj())],
            ).and_then(|x| x.i())
                .unwrap_or_else(|e| {
                    print_exception(&env);
                    println!("{}", e.display_chain().to_string());
                    panic!();
                });

            assert!(0 <= result && result < array_length);

            env.pop_local_frame(JObject::null()).unwrap_or_else(|e| {
                print_exception(&env);
                println!("{}", e.display_chain().to_string());
                panic!();
            });
        }
    }
}
