use jni::JNIEnv;
use jni::objects::JObject;
use ast_factory::Program;
use viper_sys::wrappers::viper::*;
use jni_utils::JniUtils;

pub struct AstUtils<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
}

impl<'a> AstUtils<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        AstUtils { env, jni }
    }

    pub(crate) fn check_consistency(&self, program: Program) -> Vec<JObject> {
        self.jni.seq_to_vec(self.jni.unwrap_result(
            silver::ast::Node::with(self.env).call_checkTransitively(program.to_jobject()),
        ))
    }

    pub fn pretty_print(&self, program: Program) -> String {
        let fast_pretty_printer_wrapper =
            silver::ast::pretty::FastPrettyPrinter_object::with(self.env);
        self.jni.get_string(self.jni.unwrap_result(
            fast_pretty_printer_wrapper.call_pretty_1(
                self.jni.unwrap_result(
                    fast_pretty_printer_wrapper.singleton(),
                ),
                program.to_jobject(),
            ),
        ))
    }
}
