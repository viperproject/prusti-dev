use crate::encoder::{
    snapshot,
    snapshot_encoder::{Snapshot, SnapshotEncoder},
};
use log::{debug, info, trace, warn};
use prusti_common::vir::{
    self, Expr, ExprFolder, FallibleExprFolder, Field, LocalVar, PermAmount, Position, Type,
    WithIdentifier,
};
use std::collections::HashMap;

pub struct ExprPurifier<'a> {
    snapshots: &'a HashMap<String, Box<Snapshot>>,
    self_function: Option<vir::Expr>,
    nat_arg: vir::Expr,
    create_snaps: bool,
}

impl<'a> ExprPurifier<'a> {
    pub fn new(snapshots: &'a HashMap<String, Box<Snapshot>>, nat_arg: vir::Expr) -> Self {
        ExprPurifier {
            snapshots,
            self_function: None,
            nat_arg,
            create_snaps: false,
        }
    }

    pub fn self_function(&mut self, f: Option<vir::Expr>) {
        self.self_function = f;
    }

    pub fn create_snaps(&mut self, create_snaps: bool) {
        self.create_snaps = create_snaps;
    }
}

impl<'a> ExprFolder for ExprPurifier<'a> {
    fn fold(&mut self, e: Expr) -> Expr {
        self.fallible_fold(e).unwrap()
    }
}

impl<'a> FallibleExprFolder for ExprPurifier<'a> {
    type Error = String;

    fn fallible_fold_unfolding(
        &mut self,
        name: String,
        args: Vec<Expr>,
        expr: Box<Expr>,
        perm: PermAmount,
        variant: vir::MaybeEnumVariantIndex,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        self.fallible_fold(*expr)
    }

    fn fallible_fold_variant(
        &mut self,
        base: Box<Expr>,
        variant: Field,
        p: Position,
    ) -> Result<Expr, Self::Error> {
        self.fallible_fold(*base)
    }

    fn fallible_fold_field(
        &mut self,
        receiver: Box<Expr>,
        field: Field,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        let receiver_type: Type = receiver.get_type().clone();
        if let Type::TypedRef(receiver_domain) = receiver_type {
            let mut receiver_domain = format!("Snap${}", receiver_domain); //FIXME this should come from a constant

            let variant_name = if let Expr::Variant(base, var, _) = *receiver.clone() {
                let name: String = var.name.chars().skip(5).collect(); //TODO this is probably not the best way to get the name of the variant
                receiver_domain = receiver_domain[..receiver_domain.len() - name.len()].to_string();

                Some(name)
            } else {
                None
            };
            let inner = self.fallible_fold_boxed(receiver)?;
            let field_name = field.name.to_string();
            Ok(match field_name.as_str() {
                "val_bool" | "val_int" | "val_ref" => *inner,
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
                    let purified_field_type =
                        super::translate_type(field_type, &self.snapshots).unwrap();

                    let domain_func = super::encode_field_domain_func(
                        purified_field_type,
                        field_name,
                        receiver_domain,
                        variant_name, //TODO
                    );

                    vir::Expr::DomainFuncApp(domain_func, vec![*inner], pos)
                }
            })
        } else {
            unreachable!();
        }
    }

    fn fallible_fold_local(&mut self, v: LocalVar, p: Position) -> Result<Expr, Self::Error> {
        Ok(if v.name == "__result" {
            self.self_function.clone().ok_or("Needs self_funcion")?
        } else {
            Expr::Local(
                LocalVar {
                    name: v.name,
                    typ: super::translate_type(v.typ, &self.snapshots)?,
                },
                p,
            )
        })
    }

    fn fallible_fold_cond(
        &mut self,
        guard: Box<Expr>,
        then_expr: Box<Expr>,
        else_expr: Box<Expr>,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        if let Expr::FuncApp(name, _, _, _, _) = &*then_expr {
            if name == "builtin$unreach_int" {
                return self.fallible_fold(*else_expr);
            }
        }

        if let Expr::FuncApp(name, _, _, _, _) = &*else_expr {
            if name == "builtin$unreach_int" {
                return self.fallible_fold(*then_expr);
            }
        }

        Ok(Expr::Cond(
            self.fallible_fold_boxed(guard)?,
            self.fallible_fold_boxed(then_expr)?,
            self.fallible_fold_boxed(else_expr)?,
            pos,
        ))
    }

    fn fallible_fold_func_app(
        &mut self,
        name: String,
        mut args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        match name.as_str() {
            "snap$" => {
                // This is a snapshot function. Just drop it and use its argument.
                // FIXME: We should have a proper way of discovering this.
                assert_eq!(
                    args.len(),
                    1,
                    "The snapshot function must contain only a single argument."
                );
                self.fallible_fold(args.pop().unwrap())
            }
            _ => {
                let ident_name = vir::compute_identifier(&name, &formal_args, &return_type);

                let df = snapshot::encode_mirror_function(
                    &name,
                    &formal_args,
                    &return_type,
                    &self.snapshots,
                )?;

                let mut folded_args: Vec<Expr> = args
                    .into_iter()
                    .map(|e| self.fallible_fold(e.clone()).map(|n| (e, n)))
                    .collect::<Result<Vec<(Expr, Expr)>, _>>()?
                    .into_iter()
                    .map(|(orig, e)| {
                        if !self.create_snaps {
                            Ok(e)
                        } else {
                            let typ: vir::Type = orig.get_type().clone();
                            if let vir::Type::TypedRef(predicate_name) = typ {
                                if let Some(snapshot) = self.snapshots.get(&predicate_name) {
                                    Ok(snapshot.snap_call(e))
                                } else {
                                    Ok(e)
                                }
                            } else {
                                Ok(e)
                            }
                        }
                    })
                    .collect::<Result<Vec<Expr>, String>>()?;
                folded_args.push(self.nat_arg.clone());
                Ok(Expr::DomainFuncApp(df, folded_args, pos))
            }
        }
    }

    fn fallible_fold_predicate_access_predicate(
        &mut self,
        name: String,
        arg: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(true.into())
    }

    fn fallible_fold_field_access_predicate(
        &mut self,
        receiver: Box<Expr>,
        perm_amount: PermAmount,
        pos: Position,
    ) -> Result<Expr, Self::Error> {
        Ok(true.into())
    }
}

pub struct AssertPurifier<'a> {
    snapshots: &'a HashMap<String, Box<Snapshot>>,
    nat_arg: vir::Expr,
}

impl<'a> AssertPurifier<'a> {
    pub fn new(snapshots: &'a HashMap<String, Box<Snapshot>>, nat_arg: vir::Expr) -> Self {
        AssertPurifier { snapshots, nat_arg }
    }
}

impl<'a> ExprFolder for AssertPurifier<'a> {
    fn fold_func_app(
        &mut self,
        name: String,
        mut args: Vec<Expr>,
        formal_args: Vec<LocalVar>,
        return_type: Type,
        pos: Position,
    ) -> Expr {
        let ident_name = vir::compute_identifier(&name, &formal_args, &return_type);
        let mut folded_args: Vec<Expr> = args
            .into_iter()
            .map(|e| self.fold(e.clone()))
            .collect::<Vec<Expr>>();
            
        match snapshot::encode_mirror_function(&name, &formal_args, &return_type, &self.snapshots) {
            Err(e) => {
                let fun =  Expr::FuncApp(name, folded_args, formal_args, return_type, pos);
                warn!("Not AssertPurifing {:?} because we cannot get the mirror function because {}", fun,e  );
                fun
            }
            Ok(df) => {
                
                let mut folded_domain_func_args: Vec<Expr> = folded_args.into_iter()
                    .map(|e| {
                        let typ: vir::Type = e.get_type().clone();
                        if let vir::Type::TypedRef(predicate_name) = typ {
                            if let Some(snapshot) = self.snapshots.get(&predicate_name) {
                                snapshot.snap_call(e)
                            } else {
                                e
                            }
                        } else {
                            e
                        }
                    })
                    .collect();
                folded_domain_func_args.push(self.nat_arg.clone());
                Expr::DomainFuncApp(df, folded_domain_func_args, pos)
            }
        }
    }
}
