use jni::*;
use std::fs;
use verification_context::*;
use error_chain::ChainedError;

pub struct Viper {
    jvm: JavaVM,
}

impl Viper {
    pub fn new() -> Self {
        let jar_paths: Vec<String> = fs::read_dir("/usr/lib/viper/")
            .unwrap()
            .map(|x| x.unwrap().path().to_str().unwrap().to_owned())
            .collect();

        let jvm_args = InitArgsBuilder::new()
            .version(JNIVersion::V8)
            .option(&format!("-Djava.class.path={}", jar_paths.join(":")))
            .option("-Xdebug")
            //.option("-verbose:gc")
            //.option("-Xcheck:jni")
            //.option("-XX:+CheckJNICalls")
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

        Viper { jvm }
    }

    pub fn new_verification_context(&self) -> VerificationContext {
        let env_guard = self.jvm.attach_current_thread().expect(
            "failed to attach jvm thread",
        );

        VerificationContext::new(env_guard)
    }
}
