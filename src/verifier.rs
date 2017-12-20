extern crate viper_sys;
extern crate jni;

use jni::JNIEnv;
use jni::objects::JObject;
use ast_factory::*;
use viper_sys::wrappers::viper::silicon::Silicon as SiliconWrapper;
use jni_utils::JniUtils;
use verification_result::VerificationResult;
use error_manager::ErrorManager;
use std::marker::PhantomData;

pub mod state {
    pub enum Uninitialized {}
    pub enum Stopped {}
    pub enum Started {}
}

pub struct Verifier<'a, VerifierState> {
    silicon_wrapper: SiliconWrapper<'a>,
    silicon_instance: JObject<'a>,
    jni: JniUtils<'a>,
    state: PhantomData<VerifierState>,
}

impl<'a, VerifierState> Verifier<'a, VerifierState> {
    pub fn new(env: &'a JNIEnv) -> Verifier<'a, state::Uninitialized> {
        let jni = JniUtils::new(env);
        let silicon_wrapper = SiliconWrapper::with(env);
        let silicon_instance = jni.unwrap_result(silicon_wrapper.new());

        Verifier {
            silicon_wrapper,
            silicon_instance,
            jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Uninitialized> {
    pub fn parse_command_line(self, args: Vec<&str>) -> Verifier<'a, state::Stopped> {
        {
            let args = self.jni.new_seq(
                args.iter()
                    .map(|x| self.jni.new_string(x))
                    .collect(),
            );
            self.jni.unwrap_result(
                self.silicon_wrapper.call_parseCommandLine(
                    self.silicon_instance,
                    args,
                ),
            );
        }
        Verifier {
            silicon_wrapper: self.silicon_wrapper,
            silicon_instance: self.silicon_instance,
            jni: self.jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Stopped> {
    pub fn start(self) -> Verifier<'a, state::Started> {
        self.jni.unwrap_result(self.silicon_wrapper.call_start(
            self.silicon_instance,
        ));

        Verifier {
            silicon_wrapper: self.silicon_wrapper,
            silicon_instance: self.silicon_instance,
            jni: self.jni,
            state: PhantomData,
        }
    }
}

impl<'a> Verifier<'a, state::Started> {
    pub fn verify(&self, program: Program, _: ErrorManager) -> VerificationResult {
        let java_result = self.jni.unwrap_result(self.silicon_wrapper.call_verify(
            self.silicon_instance,
            program.to_jobject(),
        ));

        println!(
            "Java verification result: {}",
            self.jni.to_string(java_result)
        );

        // TODO: convert `result` to a `VerificationResult`

        VerificationResult::Success()
    }
}
