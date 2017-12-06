use jni::sys::{JavaVM as RawJavaVM, JNIEnv as RawJNIEnv, JavaVMInitArgs, JavaVMOption,
               JNI_CreateJavaVM, JNI_FALSE, JNI_OK, JNI_VERSION_1_8};
use jni::JNIEnv;
use std::ffi::CString;
use std::ptr;
use std::os::raw::c_void;

#[link(name = "jvm")]
extern "C" {}

pub unsafe fn build_jvm(jvm_option_strings: &[&str]) -> (*mut RawJavaVM, *mut RawJNIEnv) {
    // Wrap the JVM option string slices in a vector of `CString`s.
    let mut jvm_option_cstrings: Vec<CString> = Vec::new();

    for jvm_option_string in jvm_option_strings {
        jvm_option_cstrings.push(CString::new(*jvm_option_string).unwrap());
    }

    // Create a vector of `JavaVMOption`s, each referencing a `CString`.
    let mut jvm_options: Vec<JavaVMOption> = Vec::new();

    for jvm_option_cstring in &jvm_option_cstrings {

        let jvm_option = JavaVMOption {
            optionString: jvm_option_cstring.as_ptr() as *mut i8,
            extraInfo: ptr::null_mut() as *mut c_void,
        };

        jvm_options.push(jvm_option);
    }

    // Create the JVM arguments.
    let mut jvm_arguments = JavaVMInitArgs {
        version: JNI_VERSION_1_8,
        options: jvm_options.as_mut_ptr(),
        nOptions: jvm_options.len() as i32,
        ignoreUnrecognized: JNI_FALSE,
    };

    // Initialize space for a pointer to the JNI environment.
    let mut jvm: *mut RawJavaVM = ptr::null_mut();
    let mut jni_environment: *mut RawJNIEnv = ptr::null_mut();

    // Try to instantiate the JVM.
    let result = JNI_CreateJavaVM(
        &mut jvm,
        (&mut jni_environment as *mut *mut RawJNIEnv) as *mut *mut c_void,
        (&mut jvm_arguments as *mut JavaVMInitArgs) as *mut c_void,
    );

    // There was an error while trying to instantiate the JVM.
    assert!(result == JNI_OK);

    (jvm, jni_environment)
}

pub fn print_exception(env: &JNIEnv) {
    let exception_occurred = env.exception_check().ok().unwrap();
    if exception_occurred {
        env.exception_describe().ok().unwrap();
    }
}

pub fn panic_on_exception(env: &JNIEnv) {
    let exception_occurred = env.exception_check().ok().unwrap();
    if exception_occurred {
        env.exception_describe().ok().unwrap();
        panic!();
    }
}
