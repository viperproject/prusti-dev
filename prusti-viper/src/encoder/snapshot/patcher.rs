// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use crate::encoder::{
    errors::{EncodingError, EncodingResult},
    high::types::HighTypeEncoderInterface,
    snapshot::encoder::SnapshotEncoder,
    Encoder,
};
use vir_crate::polymorphic::{self as vir, ExprFolder, FallibleExprFolder, FallibleStmtFolder};

pub(super) struct SnapshotPatcher<'p, 'v: 'p, 'tcx: 'v> {
    pub(super) snapshot_encoder: &'p mut SnapshotEncoder,
    pub(super) encoder: &'p Encoder<'v, 'tcx>,
}

impl<'p, 'v: 'p, 'tcx: 'v> FallibleExprFolder for SnapshotPatcher<'p, 'v, 'tcx> {
    type Error = EncodingError;

    fn fallible_fold_snap_app(
        &mut self,
        vir::SnapApp { mut base, .. }: vir::SnapApp,
    ) -> Result<vir::Expr, Self::Error> {
        base = self.fallible_fold_boxed(base)?;
        self.snapshot_encoder.snap_app(self.encoder, *base)
    }

    fn fallible_fold_func_app(
        &mut self,
        vir::FuncApp {
            function_name,
            type_arguments,
            mut arguments,
            formal_arguments,
            return_type,
            position,
        }: vir::FuncApp,
    ) -> Result<vir::Expr, Self::Error> {
        arguments = arguments
            .into_iter()
            .zip(formal_arguments.iter())
            .map(|(mut arg, formal_arg)| {
                arg = FallibleExprFolder::fallible_fold(self, arg)?;
                // TODO: this patches more than it should
                // so it could cover up/muddle some type errors in the VIR
                if *arg.get_type() != formal_arg.typ {
                    self.snapshot_encoder.snap_app(self.encoder, arg)
                } else {
                    Ok(arg)
                }
            })
            .collect::<Result<_, _>>()?;
        Ok(vir::Expr::FuncApp(vir::FuncApp {
            function_name,
            type_arguments,
            arguments,
            formal_arguments,
            return_type,
            position,
        }))
    }

    fn fallible_fold_domain_func_app(
        &mut self,
        vir::DomainFuncApp {
            domain_function,
            arguments,
            position,
        }: vir::DomainFuncApp,
    ) -> Result<vir::Expr, Self::Error> {
        let folded_args = arguments
            .into_iter()
            .zip(domain_function.formal_args.iter())
            .map(|(arg, formal_arg)| {
                let folded_arg = FallibleExprFolder::fallible_fold(self, arg)?;
                // TODO: same note as for fallible_fold_func_app applies
                if *folded_arg.get_type() != formal_arg.typ {
                    self.snapshot_encoder.snap_app(self.encoder, folded_arg)
                } else {
                    Ok(folded_arg)
                }
            })
            .collect::<Result<Vec<_>, _>>()?;

        Ok(vir::Expr::DomainFuncApp(vir::DomainFuncApp {
            domain_function,
            arguments: folded_args,
            position,
        }))
    }

    fn fallible_fold_field(
        &mut self,
        vir::FieldExpr {
            base: receiver,
            field,
            position,
        }: vir::FieldExpr,
    ) -> Result<vir::Expr, Self::Error> {
        match receiver {
            box vir::Expr::Variant(vir::Variant {
                base: receiver,
                variant_index: variant,
                position: pos2,
            }) => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    vir::Type::Snapshot(_) => self.snapshot_encoder.snap_variant_field(
                        self.encoder,
                        *receiver,
                        variant,
                        field,
                    ),
                    _ => Ok(vir::Expr::Field(vir::FieldExpr {
                        base: Box::new(vir::Expr::Variant(vir::Variant {
                            base: receiver,
                            variant_index: variant,
                            position: pos2,
                        })),
                        field,
                        position,
                    })),
                }
            }
            receiver => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    vir::Type::Int if field.name == "val_int" => Ok(*receiver),
                    vir::Type::Bool if field.name == "val_bool" => Ok(*receiver),

                    vir::Type::Int if field.name == "val_ref" => Ok(*receiver),
                    vir::Type::Bool if field.name == "val_ref" => Ok(*receiver),

                    vir::Type::Snapshot(_) => match field.name.as_str() {
                        "val_ref" => Ok(*receiver),
                        _ => self
                            .snapshot_encoder
                            .snap_field(self.encoder, *receiver, field),
                    },
                    _ => Ok(vir::Expr::Field(vir::FieldExpr {
                        base: receiver,
                        field,
                        position,
                    })),
                }
            }
        }
    }

    fn fallible_fold_forall(
        &mut self,
        vir::ForAll {
            variables,
            triggers,
            body,
            position,
        }: vir::ForAll,
    ) -> Result<vir::Expr, Self::Error> {
        let (patched_vars, triggers, expr) = fix_quantifier(self, variables, triggers, *body)?;
        Ok(vir::Expr::ForAll(vir::ForAll {
            variables: patched_vars,
            triggers,
            body: Box::new(expr),
            position,
        }))
    }

    fn fallible_fold_exists(
        &mut self,
        vir::Exists {
            variables,
            triggers,
            body,
            position,
        }: vir::Exists,
    ) -> Result<vir::Expr, Self::Error> {
        let (patched_vars, triggers, expr) = fix_quantifier(self, variables, triggers, *body)?;
        Ok(vir::Expr::Exists(vir::Exists {
            variables: patched_vars,
            triggers,
            body: Box::new(expr),
            position,
        }))
    }

    fn fallible_fold_downcast(
        &mut self,
        vir::DowncastExpr {
            base,
            enum_place,
            field,
        }: vir::DowncastExpr,
    ) -> Result<vir::Expr, Self::Error> {
        let base = FallibleExprFolder::fallible_fold(self, *base)?;
        let enum_expr = FallibleExprFolder::fallible_fold(self, *enum_place)?;
        if base.get_type().is_snapshot() || enum_expr.get_type().is_snapshot() {
            Ok(base)
        } else {
            Ok(vir::Expr::Downcast(vir::DowncastExpr {
                base: Box::new(base),
                enum_place: Box::new(enum_expr),
                field,
            }))
        }
    }
}

impl<'p, 'v: 'p, 'tcx: 'v> FallibleStmtFolder for SnapshotPatcher<'p, 'v, 'tcx> {
    type Error = EncodingError;

    fn fallible_fold_expr(&mut self, expr: vir::Expr) -> Result<vir::Expr, Self::Error> {
        FallibleExprFolder::fallible_fold(self, expr)
    }

    fn fallible_fold_downcast(
        &mut self,
        vir::Downcast { base, field }: vir::Downcast,
    ) -> Result<vir::Stmt, Self::Error> {
        if base.get_type().is_snapshot() {
            Ok(vir::Stmt::comment("patched out Downcast stmt"))
        } else {
            Ok(vir::Stmt::Downcast(vir::Downcast {
                base: self.fallible_fold_expr(base)?,
                field,
            }))
        }
    }
}

fn fix_quantifier(
    patcher: &mut SnapshotPatcher,
    vars: Vec<vir::LocalVar>,
    triggers: Vec<vir::Trigger>,
    mut expr: vir::Expr,
) -> EncodingResult<(Vec<vir::LocalVar>, Vec<vir::Trigger>, vir::Expr)> {
    // TODO: check is_quantifiable
    let mut patched_vars = vec![];

    // unpack triggers into Vec<Vec<Expr>>
    let mut trigger_exprs = triggers
        .into_iter()
        .map(|trigger| trigger.elements().to_vec())
        .collect::<Vec<_>>();

    for var in vars {
        match var.typ {
            vir::Type::TypedRef(_) => {
                let ty = patcher.encoder.decode_type_predicate_type(&var.typ)?;
                let patched_var = vir::LocalVar::new(
                    &var.name,
                    patcher.snapshot_encoder.encode_type(patcher.encoder, ty)?,
                );
                patched_vars.push(patched_var.clone());
                let mut fixer = QuantifierFixer { var, patched_var };
                expr = fixer.fold(expr);
                trigger_exprs = trigger_exprs
                    .into_iter()
                    .map(|trigger| trigger.into_iter().map(|expr| fixer.fold(expr)).collect())
                    .collect();
            }
            _ => patched_vars.push(var.clone()),
        }
    }
    let expr = FallibleExprFolder::fallible_fold(patcher, expr)?;

    Ok((
        patched_vars,
        trigger_exprs
            .into_iter()
            .map(|trigger| {
                trigger
                    .into_iter()
                    .map(|expr| FallibleExprFolder::fallible_fold(patcher, expr))
                    .collect::<Result<Vec<_>, _>>()
            })
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(vir::Trigger::new)
            .collect(),
        expr,
    ))
}

struct QuantifierFixer {
    var: vir::LocalVar,
    patched_var: vir::LocalVar,
}

impl ExprFolder for QuantifierFixer {
    fn fold_local(&mut self, vir::Local { variable, position }: vir::Local) -> vir::Expr {
        if variable.name == self.var.name {
            vir::Expr::local_with_pos(self.patched_var.clone(), position)
        } else {
            vir::Expr::local_with_pos(variable, position)
        }
    }
}
