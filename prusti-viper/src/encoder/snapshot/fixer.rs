use std::collections::HashMap;
use prusti_common::vir::{self, ExprFolder};
use crate::encoder::snapshot_encoder::Snapshot;
use crate::encoder::snapshot;

pub struct Fixer<'a> {
    pub snapshots: &'a HashMap<String, Box<Snapshot>>,
}

impl<'a> ExprFolder for Fixer<'a> {
    // FIXME: An almost identical function is in
    // prusti-viper/src/encoder/snapshot_spec_patcher.rs. However, that function
    // patches the expression to use a different kind of mirror function (yes,
    // we currently have two kinds of them: one for equality and other for all
    // purified functions). Once we trust our purified function encoding, we
    // should replace the mirror functions from equality with our new encoding.
    // However, for that we need to develop a strategy how we are going to check
    // the encoding of the functions.
    fn fold_func_app(
        &mut self,
        mut name: String,
        args: Vec<vir::Expr>,
        mut formal_args: Vec<vir::LocalVar>,
        return_type: vir::Type,
        pos: vir::Position
    ) -> vir::Expr {
        let type_mismatch = args.iter().zip(formal_args.iter()).any(|(arg, parameter)| {
            match (arg.get_type(), &parameter.typ) {
                (vir::Type::Domain(_), vir::Type::TypedRef(_)) |
                (vir::Type::Int, vir::Type::TypedRef(_)) |
                (vir::Type::Bool, vir::Type::TypedRef(_)) => true,
                _ => false,
            }
        });
        if type_mismatch {
            name = format!("{}{}", snapshot::MIRROR_FUNCTION_PREFIX, name);
            formal_args = formal_args.into_iter().map(|parameter| {
                vir::LocalVar {
                    name: parameter.name,
                    typ: super::translate_type(parameter.typ, self.snapshots).unwrap(),
                }
            }).collect();
        };
        vir::Expr::FuncApp(name, args, formal_args, return_type, pos)
    }
}
