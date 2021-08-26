// © 2021, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use prusti_common::vir;
use vir_crate::polymorphic::{self as polymorphic_vir, ExprFolder, FallibleExprFolder, FallibleStmtFolder};
use crate::encoder::Encoder;
use crate::encoder::errors::{EncodingError, EncodingResult};
use crate::encoder::snapshot::encoder::{UNIT_DOMAIN_NAME, SnapshotEncoder};

pub(super) struct SnapshotPatcher<'v, 'tcx: 'v> {
    pub(super) snapshot_encoder: &'v mut SnapshotEncoder,
    pub(super) encoder: &'v Encoder<'v, 'tcx>,
}

impl<'v, 'tcx: 'v> FallibleExprFolder for SnapshotPatcher<'v, 'tcx> {
    type Error = EncodingError;

    fn fallible_fold_snap_app(
        &mut self,
        e: Box<polymorphic_vir::Expr>,
        _p: polymorphic_vir::Position
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        let e = self.fallible_fold_boxed(e)?;
        self.snapshot_encoder.snap_app(self.encoder, *e)
    }

    fn fallible_fold_func_app(
        &mut self,
        name: String,
        mut args: Vec<polymorphic_vir::Expr>,
        formal_args: Vec<polymorphic_vir::LocalVar>,
        return_type: polymorphic_vir::Type,
        pos: polymorphic_vir::Position,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        args = args.into_iter()
            .zip(formal_args.iter())
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
        Ok(polymorphic_vir::Expr::FuncApp( polymorphic_vir::FuncApp {
            function_name: name,
            arguments: args,
            formal_arguments: formal_args,
            return_type,
            position: pos,
        }))
    }

    fn fallible_fold_domain_func_app(
        &mut self,
        func: polymorphic_vir::DomainFunc,
        args: Vec<polymorphic_vir::Expr>,
        pos: polymorphic_vir::Position,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        let folded_args = args.into_iter()
            .zip(func.formal_args.iter())
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

        Ok(polymorphic_vir::Expr::DomainFuncApp( polymorphic_vir::DomainFuncApp {
            domain_function: func,
            arguments: folded_args,
            position: pos,
        }))
    }

    fn fallible_fold_field(
        &mut self,
        receiver: Box<polymorphic_vir::Expr>,
        field: polymorphic_vir::Field,
        pos: polymorphic_vir::Position,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        match receiver {
            box polymorphic_vir::Expr::Variant( polymorphic_vir::Variant {base: receiver, variant_index: variant, position: pos2} ) => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    polymorphic_vir::Type::Snapshot(_) => self.snapshot_encoder.snap_variant_field(
                        self.encoder,
                        *receiver,
                        variant,
                        field,
                    ),
                    _ => Ok(polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {
                        base: box polymorphic_vir::Expr::Variant( polymorphic_vir::Variant {base: receiver, variant_index: variant, position: pos2} ),
                        field,
                        position: pos
                    })),
                }
            },
            receiver => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    polymorphic_vir::Type::Int if field.name == "val_int" => Ok(*receiver),
                    polymorphic_vir::Type::Bool if field.name == "val_bool" => Ok(*receiver),
                    polymorphic_vir::Type::Snapshot(_) => {
                        let res = match field.name.as_str() {
                            "val_ref" => Ok(*receiver),
                            _ => self.snapshot_encoder.snap_field(self.encoder, *receiver, field),
                        }?;
                        Ok(res)
                    }
                    _ => Ok(polymorphic_vir::Expr::Field( polymorphic_vir::FieldExpr {base: receiver, field, position: pos} ) ),
                }
            }
        }
    }

    fn fallible_fold_forall(
        &mut self,
        vars: Vec<polymorphic_vir::LocalVar>,
        triggers: Vec<polymorphic_vir::Trigger>,
        expr: Box<polymorphic_vir::Expr>,
        pos: polymorphic_vir::Position,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        let (patched_vars, triggers, expr) = fix_quantifier(self, vars, triggers, *expr)?;
        Ok(polymorphic_vir::Expr::ForAll( polymorphic_vir::ForAll {
            variables: patched_vars,
            triggers,
            body: box expr,
            position: pos,
        }))
    }

    fn fallible_fold_exists(
        &mut self,
        vars: Vec<polymorphic_vir::LocalVar>,
        triggers: Vec<polymorphic_vir::Trigger>,
        expr: Box<polymorphic_vir::Expr>,
        pos: polymorphic_vir::Position,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        let (patched_vars, triggers, expr) = fix_quantifier(self, vars, triggers, *expr)?;
        Ok(polymorphic_vir::Expr::Exists( polymorphic_vir::Exists {
            variables: patched_vars,
            triggers,
            body: box expr,
            position: pos,
        }))
    }

    fn fallible_fold_downcast(
        &mut self,
        base: Box<polymorphic_vir::Expr>,
        enum_expr: Box<polymorphic_vir::Expr>,
        field: polymorphic_vir::Field,
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        let base = FallibleExprFolder::fallible_fold(self, *base)?;
        let enum_expr = FallibleExprFolder::fallible_fold(self, *enum_expr)?;
        if base.get_type().is_snapshot() || enum_expr.get_type().is_snapshot() {
            Ok(base)
        } else {
            Ok(polymorphic_vir::Expr::Downcast( polymorphic_vir::DowncastExpr {
                base: box base,
                enum_place: box enum_expr,
                field,
            }))
        }
    }
}

impl<'v, 'tcx: 'v> FallibleStmtFolder for SnapshotPatcher<'v, 'tcx> {
    type Error = EncodingError;

    fn fallible_fold_expr(
        &mut self,
        expr: polymorphic_vir::Expr
    ) -> Result<polymorphic_vir::Expr, Self::Error> {
        FallibleExprFolder::fallible_fold(self, expr)
    }

    fn fallible_fold_downcast(
        &mut self,
        e: polymorphic_vir::Expr,
        f: polymorphic_vir::Field
    ) -> Result<polymorphic_vir::Stmt, Self::Error> {
        if e.get_type().is_snapshot() {
            Ok(polymorphic_vir::Stmt::comment("patched out Downcast stmt"))
        } else {
            Ok(polymorphic_vir::Stmt::Downcast( polymorphic_vir::Downcast {base: self.fallible_fold_expr(e)?, field: f} ) )
        }
    }
}

fn fix_quantifier(
    patcher: &mut SnapshotPatcher,
    vars: Vec<polymorphic_vir::LocalVar>,
    triggers: Vec<polymorphic_vir::Trigger>,
    mut expr: polymorphic_vir::Expr,
) -> EncodingResult<(
    Vec<polymorphic_vir::LocalVar>,
    Vec<polymorphic_vir::Trigger>,
    polymorphic_vir::Expr,
)> {
    // TODO: check is_quantifiable
    let mut patched_vars = vec![];

    // unpack triggers into Vec<Vec<Expr>>
    let mut trigger_exprs = triggers
        .into_iter()
        .map(|trigger| trigger
            .elements()
            .iter()
            .cloned()
            .collect::<Vec<_>>())
        .collect::<Vec<_>>();

    for var in vars {
        match var.typ {
            polymorphic_vir::Type::TypedRef(_) => {
                let ty = patcher.encoder.decode_type_predicate_type(&var.typ)?;
                let patched_var = polymorphic_vir::LocalVar::new(
                    &var.name,
                    patcher.snapshot_encoder.encode_type(patcher.encoder, ty)?,
                );
                patched_vars.push(patched_var.clone());
                let mut fixer = QuantifierFixer {
                    var,
                    patched_var,
                };
                expr = fixer.fold(expr);
                trigger_exprs = trigger_exprs
                    .into_iter()
                    .map(|trigger| trigger
                        .into_iter()
                        .map(|expr| fixer.fold(expr))
                        .collect())
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
            .map(|trigger| trigger
                .into_iter()
                .map(|expr| FallibleExprFolder::fallible_fold(patcher, expr))
                .collect::<Result<Vec<_>, _>>())
            .collect::<Result<Vec<_>, _>>()?
            .into_iter()
            .map(polymorphic_vir::Trigger::new)
            .collect(),
        expr,
    ))
}

struct QuantifierFixer {
    var: polymorphic_vir::LocalVar,
    patched_var: polymorphic_vir::LocalVar,
}

impl ExprFolder for QuantifierFixer {
    fn fold_local(
        &mut self,
        v: polymorphic_vir::LocalVar,
        pos: polymorphic_vir::Position
    ) -> polymorphic_vir::Expr {
        if v.name == self.var.name {
            polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: self.patched_var.clone(), position: pos} )
        } else {
            polymorphic_vir::Expr::Local( polymorphic_vir::Local {variable: v, position: pos} )
        }
    }
}
