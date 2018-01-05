#![allow(dead_code)]

use jni::sys::jint;
use jni::objects::JObject;
use viper_sys::wrappers::*;
use viper_sys::wrappers::viper::silver::ast;
use ast_factory::AstFactory;

jobject_wrapper!(Position);

impl<'a> AstFactory<'a> {
    pub fn new_no_position(&self) -> Position {
        let obj = self.jni.unwrap_result(
            ast::NoPosition_object::with(self.env).singleton(),
        );
        Position { obj }
    }

    pub fn new_line_column_position(&self, line: jint, column: jint) -> Position {
        let obj = self.jni.unwrap_result(
            ast::LineColumnPosition::with(self.env).new(
                line,
                column,
            ),
        );
        Position { obj }
    }

    pub fn new_identifier_position(&self, line: jint, column: jint, pos_id: &str) -> Position {
        let obj = self.jni.unwrap_result(
            ast::IdentifierPosition::with(self.env).new(
                self.jni.unwrap_result(
                    java::nio::file::Paths::with(self.env).call_get(
                        self.jni.new_string(""),
                        self.jni.new_object_array(0),
                    ),
                ),
                self.new_line_column_position(line, column).to_jobject(),
                self.jni.new_option(None),
                self.jni.new_string(pos_id),
            ),
        );
        Position { obj }
    }
}
