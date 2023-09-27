#[rustfmt::skip]
#[path = "../gen/mod.rs"]
pub mod wrappers;

use jni::{errors::Result, InitArgsBuilder, JNIEnv, JNIVersion, JavaVM};
use std::sync::Once;

pub fn print_exception(env: &JNIEnv) {
    let exception_occurred = env.exception_check().unwrap_or_else(|e| panic!("{e:?}"));
    if exception_occurred {
        env.exception_describe().unwrap_or_else(|e| panic!("{e:?}"));
    }
}

// TODO: Refactor using a LazyLock<JavaVM>
// see https://github.com/viperproject/prusti-dev/pull/1364#issuecomment-1471597370
// for further details
static INIT_JVM: Once = Once::new();
static mut JVM: Option<JavaVM> = None;

fn init_jvm() -> Result<()> {
    INIT_JVM.call_once(|| {
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

        unsafe {
            JVM = Some(jvm);
        }
    });
    Ok(())
}

pub fn get_jvm() -> Result<&'static JavaVM> {
    init_jvm()?;
    unsafe {
        if let Some(res) = JVM.as_ref() {
            Ok(res)
        } else {
            panic!("Failed to get JVM reference")
        }
    }
}
