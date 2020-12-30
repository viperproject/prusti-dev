use crate::encoder::snapshot_encoder::{Snapshot, SnapshotEncoder};
use log::{debug, info, trace, warn};
use prusti_common::vir::{self, Expr, Field, PermAmount, Position, Type, LocalVar, ExprFolder};
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

    fn fold_field(
        &mut self,
        receiver: Box<Expr>,
        field: Field,
        pos: Position,
    ) -> Expr {
        let receiver_type: Type = receiver.get_type().clone();
        if let Type::TypedRef(receiver_domain) = receiver_type {
            let receiver_domain = format!("Snap${}", receiver_domain); //FIXME this should come from a constant
            let inner = self.fold_boxed(receiver);
            let field_name = field.name.to_string();
            info!("translating field {}", field_name);
            match field_name.as_str() {
                "val_bool" | "val_int" => *inner,
                _ => {
                    let field_name: String = field_name.chars().skip(2).collect();
                    let field_type = field.typ.clone();
                    let purified_field_type = super::transalte_type(field_type, &self.snapshots);

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

    fn fold_local(&mut self, v: LocalVar, p: Position) -> Expr {
        warn!("fold_local {}", v);

        if v.name == "__result" {
            self.self_function.clone()
        }
        else {
		Expr::Local(
		    LocalVar {
		        name: v.name,
		        typ: super::transalte_type(v.typ, &self.snapshots),
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
        pos: Position
    ) -> Expr {
        true.into()
    }
}
