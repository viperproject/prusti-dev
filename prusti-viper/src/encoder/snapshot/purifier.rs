use crate::encoder::snapshot_encoder::{Snapshot, SnapshotEncoder};
use log::{debug, info, trace, warn};
use prusti_common::vir::{self, Expr, ExprFolder, Field, LocalVar, PermAmount, Position, Type};
use std::collections::HashMap;

pub struct ExprPurifier {
    pub snapshots: HashMap<String, Box<Snapshot>>,
    pub self_function: vir::Expr,
}

impl ExprFolder for ExprPurifier {
    fn fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: Position,
    ) -> Expr {
        *self.fold_boxed(expr)
    }

    fn fold_variant(&mut self, base: Box<Expr>, variant: Field, p: Position) -> Expr {
        // This should never be reached as I'm assuming that we only have the case Field(Variant) and never a bare Variant
        //   log::error!("fold_variant base: {:?} variant: {:?}", base, variant);
        *self.fold_boxed(base)
    }

    fn fold_field(&mut self, receiver: Box<Expr>, field: Field, pos: Position) -> Expr {
        let receiver_type: Type = receiver.get_type().clone();
        if let Type::TypedRef(receiver_domain) = receiver_type {
            let mut receiver_domain  = format!("Snap${}", receiver_domain); //FIXME this should come from a constant

            let variant_name = if let Expr::Variant(base, var, _) = *receiver.clone() {
                warn!("fold_field with base: {:?} variant: {:?}", base, var);
                let name: String = var.name.chars().skip(5).collect(); //TODO this is probably not the best way to get the name of the variant
                receiver_domain = receiver_domain[..receiver_domain.len() - name.len()].to_string();

                Some(name)
            } else {
                None
            };
            let inner = self.fold_boxed(receiver);
            let field_name = field.name.to_string();
            match field_name.as_str() {
                "val_bool" | "val_int" => *inner,
                "discriminant" => {
                    let domain_name = receiver_domain;
                    let snap_type = vir::Type::Domain(domain_name.to_string());
                    let arg = vir::LocalVar::new("self", snap_type);
                    let domain_func = vir::DomainFunc {
                        name: "variant$".to_string(), //TODO use constant
                        formal_args: vec![arg],
                        return_type: vir::Type::Int,
                        unique: false,
                        domain_name: domain_name.to_string(),
                    };

                    vir::Expr::DomainFuncApp(domain_func, vec![*inner], pos)
                }
                _ => {
                    let field_name: String = field_name.chars().skip(2).collect();
                    let field_type = field.typ.clone();
                    let purified_field_type = super::translate_type(field_type, &self.snapshots);
                    warn!(
                        "fold_field field_name={:?}, receiver_domain={:?}",
                        field_name, receiver_domain
                    );

                    let domain_func = super::encode_field_domain_func(
                        purified_field_type,
                        field_name,
                        receiver_domain,
                        variant_name, //TODO
                    );

                    vir::Expr::DomainFuncApp(domain_func, vec![*inner], pos)
                }
            }
        } else {
            unreachable!();
        }
    }

    fn fold_local(&mut self, v: LocalVar, p: Position) -> Expr {
        if v.name == "__result" {
            self.self_function.clone()
        } else {
            Expr::Local(
                LocalVar {
                    name: v.name,
                    typ: super::translate_type(v.typ, &self.snapshots),
                },
                p,
            )
        }
    }

    fn fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        true.into()
    }

    fn fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Expr {
        true.into()
    }
}
