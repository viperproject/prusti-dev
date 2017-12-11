use jni::JNIEnv;

pub fn print_exception(env: &JNIEnv) {
    let exception_occurred = env.exception_check().unwrap_or_else(
        |e| panic!(format!("{:?}", e)),
    );
    if exception_occurred {
        env.exception_describe().unwrap_or_else(
            |e| panic!(format!("{:?}", e)),
        );
    }
}
