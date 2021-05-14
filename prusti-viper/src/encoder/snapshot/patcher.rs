use prusti_common::vir::{self, ExprFolder, FallibleExprFolder, FallibleStmtFolder};
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
        e: Box<vir::Expr>,
        p: vir::Position
    ) -> Result<vir::Expr, Self::Error> {
        let e = self.fallible_fold_boxed(e)?;
        self.snapshot_encoder.snap_app(self.encoder, *e)
    }

    fn fallible_fold_func_app(
        &mut self,
        name: String,
        mut args: Vec<vir::Expr>,
        formal_args: Vec<vir::LocalVar>,
        return_type: vir::Type,
        pos: vir::Position,
    ) -> Result<vir::Expr, Self::Error> {
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
        Ok(vir::Expr::FuncApp(
            name,
            args,
            formal_args,
            return_type,
            pos,
        ))
    }

    fn fallible_fold_field(
        &mut self,
        receiver: Box<vir::Expr>,
        field: vir::Field,
        pos: vir::Position,
    ) -> Result<vir::Expr, Self::Error> {
        match receiver {
            box vir::Expr::Variant(receiver, variant, pos2) => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    vir::Type::Snapshot(_) => self.snapshot_encoder.snap_variant_field(
                        self.encoder,
                        *receiver,
                        variant,
                        field,
                    ),
                    _ => Ok(vir::Expr::Field(
                        box vir::Expr::Variant(receiver, variant, pos2),
                        field,
                        pos
                    )),
                }
            },
            receiver => {
                let receiver = self.fallible_fold_boxed(receiver)?;
                match receiver.get_type() {
                    vir::Type::Int if field.name == "val_int" => Ok(*receiver),
                    vir::Type::Bool if field.name == "val_bool" => Ok(*receiver),
                    vir::Type::Snapshot(_) => {
                        let res = match field.name.as_str() {
                            "val_ref" => Ok(*receiver),
                            _ => self.snapshot_encoder.snap_field(self.encoder, *receiver, field),
                        }?;
                        Ok(res)
                    }
                    _ => Ok(vir::Expr::Field(receiver, field, pos)),
                }
            }
        }
    }

    fn fallible_fold_forall(
        &mut self,
        vars: Vec<vir::LocalVar>,
        triggers: Vec<vir::Trigger>,
        expr: Box<vir::Expr>,
        pos: vir::Position,
    ) -> Result<vir::Expr, Self::Error> {
        // TODO: check is_quantifiable
        let mut expr = *expr;
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
                vir::Type::TypedRef(ref name) => {
                    let ty = self.encoder.decode_type_predicate(name)?;
                    let patched_var = vir::LocalVar::new(
                        &var.name,
                        self.snapshot_encoder.encode_type(self.encoder, ty)?,
                    );
                    patched_vars.push(patched_var.clone());
                    let mut fixer = ForallFixer {
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
        let expr = FallibleExprFolder::fallible_fold(self, expr)?;
        Ok(vir::Expr::ForAll(
            patched_vars,
            trigger_exprs
                .into_iter()
                .map(|trigger| trigger
                    .into_iter()
                    .map(|expr| FallibleExprFolder::fallible_fold(self, expr))
                    .collect::<Result<Vec<_>, _>>())
                .collect::<Result<Vec<_>, _>>()?
                .into_iter()
                .map(vir::Trigger::new)
                .collect(),
            box expr,
            pos,
        ))
    }

    fn fallible_fold_downcast(
        &mut self,
        base: Box<vir::Expr>,
        enum_expr: Box<vir::Expr>,
        field: vir::Field,
    ) -> Result<vir::Expr, Self::Error> {
        let base = FallibleExprFolder::fallible_fold(self, *base)?;
        let enum_expr = FallibleExprFolder::fallible_fold(self, *enum_expr)?;
        if base.get_type().is_snapshot() || enum_expr.get_type().is_snapshot() {
            Ok(base)
        } else {
            Ok(vir::Expr::Downcast(
                box base,
                box enum_expr,
                field,
            ))
        }
    }
}

impl<'v, 'tcx: 'v> FallibleStmtFolder for SnapshotPatcher<'v, 'tcx> {
    type Error = EncodingError;

    fn fallible_fold_expr(
        &mut self,
        expr: vir::Expr
    ) -> Result<vir::Expr, Self::Error> {
        FallibleExprFolder::fallible_fold(self, expr)
    }

    fn fallible_fold_downcast(
        &mut self,
        e: vir::Expr,
        f: vir::Field
    ) -> Result<vir::Stmt, Self::Error> {
        if e.get_type().is_snapshot() {
            Ok(vir::Stmt::comment("patched out Downcast stmt"))
        } else {
            Ok(vir::Stmt::Downcast(self.fallible_fold_expr(e)?, f))
        }
    }
}

struct ForallFixer {
    var: vir::LocalVar,
    patched_var: vir::LocalVar,
}

impl ExprFolder for ForallFixer {
    fn fold_snap_app(
        &mut self,
        expr: Box<vir::Expr>,
        pos: vir::Position
    ) -> vir::Expr {
        match *expr {
            vir::Expr::Local(v, pos) if v == self.var
                => vir::Expr::Local(self.patched_var.clone(), pos),
            _ => vir::Expr::SnapApp(expr, pos),
        }
    }

    fn fold_local(
        &mut self,
        v: vir::LocalVar,
        pos: vir::Position
    ) -> vir::Expr {
        if v == self.var {
            vir::Expr::Local(self.patched_var.clone(), pos)
        } else {
            vir::Expr::Local(v, pos)
        }
    }
}
