use super::Encoder;
use super::errors::{ErrorCtxt, SpannedEncodingResult};
use vir_crate::polymorphic::{
    self as vir, ExprWalker, StmtWalker, compute_identifier,
};
use rustc_hash::FxHashSet;

pub(super) fn resolve_leak_checks(
    encoder: &Encoder,
    method: vir::CfgMethod,
) -> SpannedEncodingResult<vir::CfgMethod> {
    let mut finder = ResourceAccessFinder {
        used_resources: FxHashSet::default(),
    };
    vir::utils::walk_method(&method, &mut finder);
    method.flat_map_statements(|stmt| -> SpannedEncodingResult<_> {
        match stmt {
            vir::Stmt::LeakCheck(vir::LeakCheck {
                scope_id,
                place,
                position,
            }) => {
                let mut checks = Vec::new();
                for (identifier, func_name) in &finder.used_resources {
                    if !encoder.has_leak_checks(identifier)? {
                        continue;
                    }
                    let check_pos =
                        encoder.error_manager().duplicate_position(position);
                    let error_ctxt = match place {
                        vir::LeakCheckPlace::Function => {
                            ErrorCtxt::PostconditionObligationLeak(
                                func_name.clone(),
                                )
                        }
                        vir::LeakCheckPlace::Loop => {
                            ErrorCtxt::LoopObligationLeak(func_name.clone())
                        }
                    };
                    encoder
                        .error_manager()
                        .set_error(check_pos, error_ctxt);
                    checks.push(vir::Stmt::Assert(vir::Assert {
                        expr: encoder
                            .get_leak_check(identifier, scope_id)?
                            .set_pos(check_pos),
                            position: check_pos,
                    }));
                }
                Ok(checks)
            }
            _ => Ok(vec![stmt]),
        }
    })
}

struct ResourceAccessFinder {
    used_resources: FxHashSet<(vir::FunctionIdentifier, String)>,
}

impl ExprWalker for ResourceAccessFinder {
    fn walk_resource_access(&mut self, vir::ResourceAccess {
        name,
        args,
        formal_arguments,
        ..
    }: &vir::ResourceAccess) {
        let identifier: vir::FunctionIdentifier =
            compute_identifier(name, &[], formal_arguments, &vir::Type::Bool).into();
        // TODO use something more robust here (e.g. systematically reverse the name encoding?):
        let user_friendly_name = if name.starts_with("m_") {
            name.as_str()[2..].to_string()
        } else {
            name.clone()
        };
        self.used_resources
            .insert((identifier, user_friendly_name));
        for arg in args {
            ExprWalker::walk(self, arg);
        }
    }
}

impl StmtWalker for ResourceAccessFinder {
    fn walk_expr(&mut self, expr: &vir::Expr) {
        ExprWalker::walk(self, expr);
    }
}
