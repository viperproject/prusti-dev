use jni::{
    errors::Result as JNIResult,
    objects::{JObject, JString},
    JNIEnv,
};
use systest::{get_jvm, print_exception, wrappers::*};

fn string_to_jobject<'a>(env: &JNIEnv<'a>, string: &str) -> JNIResult<JObject<'a>> {
    Ok(JObject::from(env.new_string(string.to_owned())?))
}

fn jobject_to_string(env: &JNIEnv<'_>, obj: JObject) -> JNIResult<String> {
    Ok(String::from(env.get_string(JString::from(obj))?))
}

#[test]
fn test_jvm_builtin_classes() {
    let jvm = get_jvm().expect("failed go get jvm reference");

    let env = jvm
        .attach_current_thread()
        .expect("failed to attach jvm thread");

    for int_value in -10..10 {
        for array_length in 1..50 {
            env.with_local_frame(16, || {
                let integer_value = java::lang::Integer::with(&env).new(int_value)?;

                let int_array =
                    env.new_object_array(array_length, "java/lang/Integer", integer_value)?;
                let int_array = unsafe { JObject::from_raw(int_array) };

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

    for int_value in -10..10 {
        env.with_local_frame(16, || {
            let integer_value = java::lang::Integer::with(&env).new(int_value)?;
            assert!(java::lang::Integer::with(&env).get_value(integer_value)? == int_value);
            let new_wal = int_value + 2;
            java::lang::Integer::with(&env).set_value(integer_value, new_wal)?;
            assert!(java::lang::Integer::with(&env).get_value(integer_value)? == new_wal);

            Ok(JObject::null())
        })
        .unwrap_or_else(|e| {
            print_exception(&env);
            panic!("{} source: {:?}", e, std::error::Error::source(&e));
        });
    }

    env.with_local_frame(16, || {
        let error_wrapper = java::lang::Error::with(&env);

        // Initalize error and check its content
        let innitial_message = "First error message".to_string();
        let error = error_wrapper.new(string_to_jobject(&env, &innitial_message)?)?;
        assert!(
            jobject_to_string(&env, error_wrapper.get_detailMessage(error)?)? == innitial_message
        );

        // Update the error object and check that the content has changed accordingly
        let another_message = "Second message".to_string();
        error_wrapper.set_detailMessage(error, string_to_jobject(&env, &another_message)?)?;
        assert!(
            jobject_to_string(&env, error_wrapper.get_detailMessage(error)?)? == another_message
        );

        // Try calling the getMessage method to achieve the same result
        assert!(jobject_to_string(&env, error_wrapper.call_getMessage(error)?)? == another_message);

        Ok(JObject::null())
    })
    .unwrap_or_else(|e| {
        print_exception(&env);
        panic!("{} source: {:?}", e, std::error::Error::source(&e));
    });
}
