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

macro_rules! map_to_jobject {
    ($item:expr) => (
        $item.map(|x| x.to_jobject())
    );
}

macro_rules! map_to_jobjects {
    ($items:expr) => (
        map_to_jobject!($items.iter()).collect()
    );
}

jobject_wrapper!(Program);
jobject_wrapper!(Method);
jobject_wrapper!(Seqn);
jobject_wrapper!(Stmt);
jobject_wrapper!(Expr);

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
        let obj = self.jni.unwrap_result(ast::Program::with(self.env).new(
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(
                map_to_jobjects!(
                    methods
                ),
            ),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Program { obj }
    }

    pub fn new_method(
        &self,
        name: &str,
        body: Option<&Seqn>,
        pres: Vec<&Expr>,
        posts: Vec<&Expr>,
    ) -> Method<'a> {
        let obj = self.jni.unwrap_result(ast::Method::with(self.env).new(
            self.jni.new_string(name),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(vec![]),
            self.jni.new_seq(
                map_to_jobjects!(pres),
            ),
            self.jni.new_seq(
                map_to_jobjects!(posts),
            ),
            self.jni.new_option(body.map(
                |x| x.to_jobject(),
            )),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Method { obj }
    }

    pub fn new_seqn(&self, stmts: Vec<&Stmt>) -> Seqn<'a> {
        let obj = self.jni.unwrap_result(ast::Seqn::with(self.env).new(
            self.jni.new_seq(
                map_to_jobjects!(stmts),
            ),
            self.jni.new_seq(vec![]),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Seqn { obj }
    }

    pub fn new_assert(&self, expr: &Expr) -> Stmt<'a> {
        let obj = self.jni.unwrap_result(ast::Assert::with(self.env).new(
            expr.to_jobject(),
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Stmt { obj }
    }

    pub fn new_true_lit(&self) -> Expr<'a> {
        let obj = self.jni.unwrap_result(ast::TrueLit::with(self.env).new(
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Expr { obj }
    }

    pub fn new_false_lit(&self) -> Expr<'a> {
        let obj = self.jni.unwrap_result(ast::FalseLit::with(self.env).new(
            self.new_no_position(),
            self.new_no_info(),
            self.new_no_trafos(),
        ));
        Expr { obj }
    }
}
