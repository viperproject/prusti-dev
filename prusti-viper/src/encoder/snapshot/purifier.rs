use crate::encoder::snapshot_encoder::{Snapshot, SnapshotEncoder};
use log::{debug, info, trace};
use prusti_common::vir;
use std::collections::HashMap;

pub struct ExprPurifier {
    pub old_formal_args: Vec<vir::LocalVar>,
    pub snapshots: HashMap<String, Box<Snapshot>>,
}

impl ExprPurifier {
    pub fn transalte_type(&self, t: vir::Type) -> vir::Type {
        match t {
            vir::Type::TypedRef(name) => match name.as_str() {
                "i32" => vir::Type::Int,
                "bool" => vir::Type::Bool,
                _ => {
                    let domain_name = self
                        .snapshots
                        .get(&name)
                        .and_then(|snap| snap.domain())
                        .map(|domain| domain.name)
                        .expect(&format!("No matching domain for '{}'", name));

                    vir::Type::Domain(domain_name)
                }
            },
            o @ _ => o,
        }
    }
}

impl vir::ExprFolder for ExprPurifier {
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<vir::Expr>,
        expr: Box<vir::Expr>,
        perm: vir::PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: vir::Position,
    ) -> vir::Expr {
        *self.fold_boxed(expr)
    }

    fn fold_field(
        &mut self,
        receiver: Box<vir::Expr>,
        field: vir::Field,
        pos: vir::Position,
    ) -> vir::Expr {
        let receiver_type: vir::Type = receiver.get_type().clone();
        if let vir::Type::TypedRef(receiver_domain) = receiver_type {
            let receiver_domain = format!("Snap${}", receiver_domain);
            let inner = self.fold_boxed(receiver);
            let field_name = field.name.to_string();
            info!("translating field {}", field_name);
            match field_name.as_str() {
                "val_bool" | "val_int" => *inner,
                _ => {
                    let field_name: String = field_name.chars().skip(2).collect();
                    let field_type = field.typ.clone();
                    let purified_field_type = self.transalte_type(field_type);

                    let domain_func = super::encode_field_domain_func(
                        purified_field_type,
                        field_name,
                        receiver_domain,
                    );

                    vir::Expr::DomainFuncApp(domain_func, vec![*inner], pos)
                }
            }
        } else {
            unreachable!();
        }
    }

    fn fold_local(&mut self, v: vir::LocalVar, p: vir::Position) -> vir::Expr {
        vir::Expr::Local(
            vir::LocalVar {
                name: v.name,
                typ: self.transalte_type(v.typ),
            },
            p,
        )
    }
}
