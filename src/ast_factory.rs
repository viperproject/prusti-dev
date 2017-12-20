#![allow(dead_code)]

use jni::JNIEnv;
use jni::objects::JObject;
use jni_utils::JniUtils;
#[allow(unused_imports)]
use viper_sys::wrappers::*;
#[allow(unused_imports)]
use viper_sys::wrappers::viper::silver::ast;

pub struct AstFactory<'a> {
    env: &'a JNIEnv<'a>,
    jni: JniUtils<'a>,
}

macro_rules! jobject_wrapper {
    ($name:ident) => (
        pub struct $name<'a> { obj: JObject<'a> }
        impl<'a> $name<'a> {
            fn new(obj: JObject<'a>) -> Self {
                $name { obj }
            }
            pub fn to_jobject(&self) -> JObject {
                self.obj
            }
        }
    );
}

jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Seqn);
jobject_wrapper!(Stmt);
jobject_wrapper!(Exp);

impl<'a> AstFactory<'a> {
    pub fn new(env: &'a JNIEnv) -> Self {
        let jni = JniUtils::new(env);
        AstFactory { env, jni }
    }

    fn new_no_position(&self) -> JObject {
        self.jni.unwrap_result(
            ast::NoPosition_object::with(self.env).singleton(),
        )
    }

    fn new_no_info(&self) -> JObject {
        self.jni.unwrap_result(
            ast::NoInfo_object::with(self.env).singleton(),
        )
    }

    fn new_no_trafos(&self) -> JObject {
        self.jni.unwrap_result(
            ast::NoTrafos_object::with(self.env).singleton(),
        )
    }

    pub fn new_program(&self, methods: Vec<&Method>) -> Program<'a> {
        let obj: JObject = self.jni.unwrap_result(ast::Program::with(self.env).new(
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(
                methods.iter().map(|x| x.to_jobject()).collect(),
            ),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Program { obj }
    }

    pub fn new_method(&self, name: &str, body: Option<&Seqn>) -> Method<'a> {
        let obj: JObject = self.jni.unwrap_result(ast::Method::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_option(body.map(
                |x| x.to_jobject(),
            )),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Method { obj }
    }
}
