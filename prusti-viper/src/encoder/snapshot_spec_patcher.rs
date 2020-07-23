// © 2020, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use encoder::{Encoder, snapshot_encoder};
use prusti_common::vir::{ExprFolder, compute_identifier};
use prusti_common::vir;
use encoder::snapshot_encoder::Snapshot;

pub struct SnapshotSpecPatcher<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> SnapshotSpecPatcher<'p, 'v, 'r, 'a, 'tcx> {
    pub fn new(encoder: &'p Encoder<'v, 'r, 'a, 'tcx>) -> Self {
        SnapshotSpecPatcher {
            encoder,
        }
    }

    pub fn patch_spec(&self, spec: vir::Expr) -> vir::Expr {
        PostSnapshotPatcher {
            encoder: self.encoder
        }.fold(spec)
    }
}

struct PostSnapshotPatcher<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> {
    encoder: &'p Encoder<'v, 'r, 'a, 'tcx>,
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> PostSnapshotPatcher<'p, 'v, 'r, 'a, 'tcx> {
    fn patch_cmp_call(&self, args: Vec<vir::Expr>, cmp: vir::BinOpKind) -> vir::Expr {
        assert_eq!(args.len(), 2);
        let lhs_is_snap = self.has_snap_type(&args[0]);
        let rhs_is_snap = self.has_snap_type(&args[1]);

        let (lhs, rhs) = if (lhs_is_snap && rhs_is_snap)
            || (!lhs_is_snap && !rhs_is_snap) {
            (
                args[0].clone(),
                args[1].clone()
            )
        } else if lhs_is_snap /* && !rhs_is_snap */ {
            (
                args[0].clone(),
                self.get_snapshot(&args[0]).get_snap_call(args[1].clone())
            )
        } else /* rhs_is_snap && !lhs_is_snap */ {
            (
                self.get_snapshot(&args[1]).get_snap_call(args[0].clone()),
                args[1].clone()
            )
        };

        vir::Expr::BinOp(
            cmp,
            box lhs,
            box rhs,
            vir::Position::default()
        )
    }

    fn has_snap_type(&self, expr: &vir::Expr) -> bool {
        if expr.is_place() || expr.is_call() {
            match expr.get_type() {
                vir::Type::Domain(_) => true,
                _ => false,
            }
        } else {
            false
        }
    }

    fn get_snapshot(&self, expr: &vir::Expr) -> Box<Snapshot> {
        match expr.get_type() {
            vir::Type::Domain(snapshot_name) => {
                self.encoder.get_snapshot(snapshot_name.to_string())
            },
            _ => unreachable!(),
        }
    }
}

impl<'p, 'v: 'p, 'r: 'v, 'a: 'r, 'tcx: 'a> ExprFolder for PostSnapshotPatcher<'p, 'v, 'r, 'a, 'tcx> {
    fn fold_func_app(
        &mut self,
        name: String,
        args: Vec<vir::Expr>,
        formal_args: Vec<vir::LocalVar>,
        return_type: vir::Type,
        pos: vir::Position,
    ) -> vir::Expr {
        let args : Vec<_> = args.into_iter().map(|e| self.fold(e)).collect();

        // patch function calls that internally use snapshots
        if args.iter().any(|a| self.has_snap_type(a)) {
            match name.as_str() {
                // equalities, e.g. PartialEq::eq(__result, x), need to be patched as __result
                // is now a snapshot whereas x is not; the desired result is
                // __result == snapshot(x)
                snapshot_encoder::SNAPSHOT_EQUALS => {
                    return self.patch_cmp_call(args, vir::BinOpKind::EqCmp);
                }
                snapshot_encoder::SNAPSHOT_NOT_EQUALS => {
                    return self.patch_cmp_call(args, vir::BinOpKind::NeCmp);
                }
                _ => {
                    // TODO CMFIXME refactor into its own function
                    // we need to rectify cases in which there is a mismatch between the
                    // functions formal arguments (which do not involve snapshots)
                    // and its actual arguments (which may involve snapshots)
                    let found_mismatch = formal_args
                        .iter()
                        .zip(args.iter())
                        .any(|(f, a)| f.typ != *a.get_type());

                    if found_mismatch { // TODO CMFIXME: using mirrors is not enough when dealing with nested calls
                        let mirror_func = self.encoder.encode_pure_snapshot_mirror(
                            compute_identifier(&name, &formal_args, &return_type),
                            &formal_args,
                            &return_type
                        ).unwrap(); // TODO CMFIXME fails if unsupported

                        let patched_args = args
                            .into_iter()
                            .map(|a| // TODO CMFIXME simplify
                                if a.is_place() { // for constants
                                    match a.get_type() {
                                        vir::Type::TypedRef(predicate_name) => {
                                            let snapshot = self.encoder
                                                .encode_snapshot_use(
                                                    predicate_name.to_string()
                                                );
                                            if snapshot.is_defined() {
                                                snapshot.get_snap_call(a)
                                            } else {
                                                a
                                            }
                                        }
                                        _ => a,
                                    }
                                } else {
                                    a
                                }
                            )
                            .collect();

                        return vir::Expr::DomainFuncApp(
                            mirror_func,
                            patched_args,
                            pos,
                        );
                    }
                }
            }
        }

        vir::Expr::FuncApp(
            name,
            args,
            formal_args,
            return_type,
            pos
        )
    }
}