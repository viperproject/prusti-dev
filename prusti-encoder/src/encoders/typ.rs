use prusti_rustc_interface::{
    index::vec::IndexVec,
    middle::mir,
    middle::ty,
    //span::def_id::DefId,
};
use rustc_type_ir::sty::TyKind;
use task_encoder::{
    TaskEncoder,
    TaskEncoderDependencies,
};
use crate::vir;

pub struct TypeEncoder;

#[derive(Clone, Debug)]
pub enum TypeEncoderError {
    UnsupportedType,
}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutputRef<'vir> {
    pub snapshot_name: &'vir str,
    pub predicate_name: &'vir str,
    pub snapshot: vir::Type<'vir>,
    pub function_unreachable: &'vir str,
    pub field_read: vir::BumpVec<'vir, &'vir str>,
    pub field_write: vir::BumpVec<'vir, &'vir str>,
    pub field_projection_p: vir::BumpVec<'vir, &'vir str>,
    pub method_refold: &'vir str,
}
impl<'vir, 'tcx> task_encoder::OutputRefAny<'vir, 'tcx> for TypeEncoderOutputRef<'vir> {}

#[derive(Clone, Debug)]
pub struct TypeEncoderOutput<'vir> {
    pub snapshot: vir::Domain<'vir>,
    pub predicate: vir::Predicate<'vir>,
    // TODO: these should be generated on demand, put into tiny encoders
    pub function_unreachable: vir::Function<'vir>,
    pub field_projection_p: vir::BumpVec<'vir, vir::Function<'vir>>,
    pub method_refold: vir::Method<'vir>,
}

use std::cell::RefCell;
thread_local! {
    static CACHE: task_encoder::CacheStaticRef<TypeEncoder> = RefCell::new(Default::default());
}

impl TaskEncoder for TypeEncoder {
    type TaskDescription<'vir, 'tcx> = ty::Ty<'tcx> where 'tcx: 'vir;

    type OutputRef<'vir, 'tcx> = TypeEncoderOutputRef<'vir> where 'tcx: 'vir;
    type OutputFullLocal<'vir, 'tcx> = TypeEncoderOutput<'vir> where 'tcx: 'vir;
    //type OutputFullDependency<'vir, 'tcx> = TypeEncoderOutputDep<'vir> where 'tcx: 'vir;

    type EncodingError = TypeEncoderError;

    fn with_cache<'vir, 'tcx, F, R>(f: F) -> R
        where 'tcx: 'vir, F: FnOnce(&'vir task_encoder::CacheRef<'vir, 'tcx, TypeEncoder>) -> R,
    {
        CACHE.with(|cache| {
            // SAFETY: the 'vir and 'tcx given to this function will always be
            //   the same (or shorter) than the lifetimes of the VIR arena and
            //   the rustc type context, respectively
            let cache = unsafe { std::mem::transmute(cache) };
            f(cache)
        })
    }

    fn task_to_key<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::TaskKey<'vir, 'tcx>
        where 'tcx: 'vir
    {
        *task
    }

    /*
    fn task_to_output_ref<'vir, 'tcx>(task: &Self::TaskDescription<'vir, 'tcx>) -> Self::OutputRef<'vir, 'tcx>
        where 'tcx: 'vir
    {
        let (snapshot, predicate) = match task.kind() {
            TyKind::Bool => ("s_Bool", "p_Bool"),
            _ => panic!(),
        };
        crate::with_vcx(|vcx| TypeEncoderOutputDep {
            snapshot: vcx.alloc_str(snapshot),
            predicate: vcx.alloc_str(predicate),
        })
    }
    */

    fn do_encode_full<'vir, 'tcx>(
        task_key: &Self::TaskKey<'vir, 'tcx>,
        deps: &mut TaskEncoderDependencies<'vir, 'tcx>,
    ) -> Result<(
        Self::OutputFullLocal<'vir, 'tcx>,
        Self::OutputFullDependency<'vir, 'tcx>,
    ), (
        Self::EncodingError,
        Option<Self::OutputFullDependency<'vir, 'tcx>>,
    )> {
        fn mk_unreachable<'vir>(vcx: &'vir vir::VirCtxt, snapshot_name: &'vir str, snapshot_ty: vir::Type<'vir>) -> vir::Function<'vir> {
            vcx.alloc(vir::FunctionData {
                name: crate::vir_format!(vcx, "{snapshot_name}_unreachable"), // TODO: pass from outside?
                args: vir::bvec![in &vcx.arena],
                ret: snapshot_ty,
                pres: vir::bvec![in &vcx.arena; vcx.alloc(vir::ExprData::Todo("false"))],
                posts: vir::bvec![in &vcx.arena],
                expr: None,
            })
        }
        fn mk_refold<'vir>(vcx: &'vir vir::VirCtxt, predicate_name: &'vir str, snapshot_ty: vir::Type<'vir>) -> vir::Method<'vir> {
            vcx.alloc(vir::MethodData {
                name: crate::vir_format!(vcx, "refold_{predicate_name}"),
                args: vir::bvec![in &vcx.arena;
                    vcx.alloc(vir::LocalDeclData {
                        name: "_p",
                        ty: vcx.alloc(vir::TypeData::Ref),
                        expr: None,
                    }),
                    vcx.alloc(vir::LocalDeclData {
                        name: "_s_old",
                        ty: snapshot_ty,
                        expr: None,
                    }),
                    vcx.alloc(vir::LocalDeclData {
                        name: "_s_new",
                        ty: snapshot_ty,
                        expr: None,
                    }),
                ],
                rets: vir::bvec![in &vcx.arena],
                pres: vir::bvec![in &vcx.arena;
                    vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                        target: predicate_name,
                        args: vir::bvec![in &vcx.arena;
                            vcx.mk_local_ex("_p"),
                            vcx.mk_local_ex("_s_old"),
                        ]
                    }))),
                ],
                posts: vir::bvec![in &vcx.arena;
                    vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                        target: predicate_name,
                        args: vir::bvec![in &vcx.arena;
                            vcx.mk_local_ex("_p"),
                            vcx.mk_local_ex("_s_new"),
                        ]
                    }))),
                ],
                blocks: None,
            })
        }
        crate::with_vcx(|vcx| match task_key.kind() {
            TyKind::Bool => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Bool"));
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot_name: "s_Bool",
                    predicate_name: "p_Bool",
                    snapshot: ty_s,
                    function_unreachable: "s_Bool_unreachable",
                    field_read: vir::bvec![in &vcx.arena],
                    field_write: vir::bvec![in &vcx.arena],
                    field_projection_p: vir::bvec![in &vcx.arena],
                    method_refold: "refold_p_Bool",
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain s_Bool {
                        function s_Bool_cons(Bool): s_Bool;
                        function s_Bool_val(s_Bool): Bool;
                        axiom_inverse(s_Bool_cons, s_Bool_val);
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate p_Bool(self_p: Ref, self_s: s_Bool) },
                    function_unreachable: mk_unreachable(vcx, "s_Bool", ty_s),
                    method_refold: mk_refold(vcx, "p_Bool", ty_s),
                    field_projection_p: vir::bvec![in &vcx.arena],
                }, ()))
            }
            TyKind::Int(int_kind) => {
                let (name_s, name_p) = match int_kind {
                    ty::IntTy::Isize => ("s_Int_isize", "p_Int_isize"),
                    ty::IntTy::I8 => ("s_Int_i8", "p_Int_i8"),
                    ty::IntTy::I16 => ("s_Int_i16", "p_Int_i16"),
                    ty::IntTy::I32 => ("s_Int_i32", "p_Int_i32"),
                    ty::IntTy::I64 => ("s_Int_i64", "p_Int_i64"),
                    ty::IntTy::I128 => ("s_Int_i128", "p_Int_i128"),
                };
                let name_cons = crate::vir_format!(vcx, "{name_s}_cons");
                let name_val = crate::vir_format!(vcx, "{name_s}_val");
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot_name: name_s,
                    predicate_name: name_p,
                    snapshot: ty_s,
                    function_unreachable: crate::vir_format!(vcx, "{name_s}_unreachable"),
                    field_read: vir::bvec![in &vcx.arena],
                    field_write: vir::bvec![in &vcx.arena],
                    field_projection_p: vir::bvec![in &vcx.arena],
                    method_refold: crate::vir_format!(vcx, "refold_{name_p}"),
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain [name_s] {
                        function [name_cons](Int): [ty_s];
                        function [name_val]([ty_s]): Int;
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate [name_p](self_p: Ref, self_s: [ty_s]) },
                    function_unreachable: mk_unreachable(vcx, name_s, ty_s),
                    method_refold: mk_refold(vcx, name_p, ty_s),
                    field_projection_p: vir::bvec![in &vcx.arena],
                }, ()))
            }
            TyKind::Uint(int_kind) => {
                let (name_s, name_p) = match int_kind {
                    ty::UintTy::Usize => ("s_Uint_usize", "p_Uint_usize"),
                    ty::UintTy::U8 => ("s_Uint_u8", "p_Uint_u8"),
                    ty::UintTy::U16 => ("s_Uint_u16", "p_Uint_u16"),
                    ty::UintTy::U32 => ("s_Uint_u32", "p_Uint_u32"),
                    ty::UintTy::U64 => ("s_Uint_u64", "p_Uint_u64"),
                    ty::UintTy::U128 => ("s_Uint_u128", "p_Uint_u128"),
                };
                let name_cons = crate::vir_format!(vcx, "{name_s}_cons");
                let name_val = crate::vir_format!(vcx, "{name_s}_val");
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot_name: name_s,
                    predicate_name: name_p,
                    snapshot: ty_s,
                    function_unreachable: crate::vir_format!(vcx, "{name_s}_unreachable"),
                    field_read: vir::bvec![in &vcx.arena],
                    field_write: vir::bvec![in &vcx.arena],
                    field_projection_p: vir::bvec![in &vcx.arena],
                    method_refold: crate::vir_format!(vcx, "refold_{name_p}"),
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain [name_s] {
                        function [name_cons](Int): [ty_s];
                        function [name_val]([ty_s]): Int;
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate [name_p](self_p: Ref, self_s: [ty_s]) },
                    function_unreachable: mk_unreachable(vcx, name_s, ty_s),
                    method_refold: mk_refold(vcx, name_p, ty_s),
                    field_projection_p: vir::bvec![in &vcx.arena],
                }, ()))
            }
            TyKind::Tuple(tys) if tys.len() == 0 => {
                let ty_s = vcx.alloc(vir::TypeData::Domain("s_Tuple0"));
                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot_name: "s_Tuple0",
                    predicate_name: "p_Tuple0",
                    snapshot: ty_s,
                    function_unreachable: "s_Tuple0_unreachable",
                    field_read: vir::bvec![in &vcx.arena],
                    field_write: vir::bvec![in &vcx.arena],
                    field_projection_p: vir::bvec![in &vcx.arena],
                    method_refold: "refold_p_Tuple0",
                });
                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain s_Tuple0 {
                        function s_Tuple0_cons(): [ty_s];
                    } },
                    predicate: crate::vir_predicate! { vcx; predicate p_Tuple0(self_p: Ref, self_s: [ty_s]) },
                    function_unreachable: mk_unreachable(vcx, "s_Tuple0", ty_s),
                    method_refold: mk_refold(vcx, "p_Tuple0", ty_s),
                    field_projection_p: vir::bvec![in &vcx.arena],
                }, ()))
            }
            TyKind::Adt(adt_def, substs) if adt_def.is_struct() => {
                let did_name = vcx.tcx.item_name(adt_def.did()).to_ident_string();

                let name_s = crate::vir_format!(vcx, "s_Adt_{did_name}");
                let name_p = crate::vir_format!(vcx, "p_Adt_{did_name}");
                let mut field_read_names = vir::bvec![in &vcx.arena];
                let mut field_write_names = vir::bvec![in &vcx.arena];
                let mut field_projection_p_names = vir::bvec![in &vcx.arena];
                for (idx, field) in adt_def.all_fields().enumerate() {
                    let ty_out = deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs)).unwrap();
                    field_read_names.push(crate::vir_format!(vcx, "{name_s}_read_{idx}"));
                    field_write_names.push(crate::vir_format!(vcx, "{name_s}_write_{idx}"));
                    field_projection_p_names.push(crate::vir_format!(vcx, "{name_p}_field_{idx}"));
                }

                deps.emit_output_ref::<Self>(*task_key, TypeEncoderOutputRef {
                    snapshot_name: name_s,
                    predicate_name: name_p,
                    snapshot: vcx.alloc(vir::TypeData::Domain(name_s)),
                    function_unreachable: crate::vir_format!(vcx, "{name_s}_unreachable"),
                    field_read: field_read_names,
                    field_write: field_write_names,
                    field_projection_p: field_projection_p_names,
                    method_refold: crate::vir_format!(vcx, "refold_{name_p}"),
                });
                let ty_s = vcx.alloc(vir::TypeData::Domain(name_s));

                let field_ty_out = adt_def.all_fields()
                    .map(|field| deps.require_ref::<crate::encoders::TypeEncoder>(field.ty(vcx.tcx, substs)).unwrap())
                    .collect::<Vec<_>>();

                let mut funcs: Vec<vir::DomainFunction<'vir>> = vec![];
                let mut axioms: Vec<vir::DomainAxiom<'vir>> = vec![];

                funcs.push(vcx.alloc(vir::DomainFunctionData {
                    unique: false,
                    name: crate::vir_format!(vcx, "{name_s}_cons"),
                    args: vir::BumpVec::from_iter_in(
                        field_ty_out.iter()
                            .map(|field_ty_out| field_ty_out.snapshot),
                        &vcx.arena,
                    ),
                    ret: ty_s,
                }));

                let mut field_projection_p = vir::bvec![in &vcx.arena];
                for (idx, field) in adt_def.all_fields().enumerate() {
                    let ty_out = &field_ty_out[idx];

                    let name_r = crate::vir_format!(vcx, "{name_s}_read_{idx}");
                    funcs.push(crate::vir_domain_func! { vcx; function [name_r]([ty_s]): [ty_out.snapshot] });

                    let name_w = crate::vir_format!(vcx, "{name_s}_write_{idx}");
                    funcs.push(crate::vir_domain_func! { vcx; function [name_w]([ty_s], [ty_out.snapshot]): [ty_s] });

                    field_projection_p.push(vcx.alloc(vir::FunctionData {
                        name: crate::vir_format!(vcx, "{name_p}_field_{idx}"),
                        args: vir::bvec![in &vcx.arena;
                            vcx.mk_local_decl("self", &vir::TypeData::Ref),
                        ],
                        ret: &vir::TypeData::Ref,
                        pres: vir::bvec![in &vcx.arena],
                        posts: vir::bvec![in &vcx.arena],
                        expr: None,
                    }));
                }

                for (write_idx, write_ty_out) in field_ty_out.iter().enumerate() {
                    for (read_idx, read_ty_out) in field_ty_out.iter().enumerate() {
                        axioms.push(vcx.alloc(vir::DomainAxiomData {
                            name: crate::vir_format!(vcx, "ax_{name_s}_write_{write_idx}_read_{read_idx}"),
                            expr: if read_idx == write_idx {
                                vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                                    qvars: vir::bvec![in &vcx.arena;
                                        vcx.mk_local_decl("self", ty_s),
                                        vcx.mk_local_decl("val", write_ty_out.snapshot),
                                    ],
                                    triggers: vir::bvec![in &vcx.arena;
                                        vcx.mk_func_app(
                                            crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                            &[vcx.mk_func_app(
                                                crate::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                                &[
                                                    vcx.mk_local_ex("self"),
                                                    vcx.mk_local_ex("val"),
                                                ],
                                            )],
                                        ),
                                    ],
                                    body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                        kind: vir::BinOpKind::CmpEq,
                                        lhs: vcx.mk_func_app(
                                            crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                            &[vcx.mk_func_app(
                                                crate::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                                &[
                                                    vcx.mk_local_ex("self"),
                                                    vcx.mk_local_ex("val"),
                                                ],
                                            )],
                                        ),
                                        rhs: vcx.mk_local_ex("val"),
                                    }))),
                                })))
                            } else {
                                vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                                    qvars: vir::bvec![in &vcx.arena;
                                        vcx.mk_local_decl("self", ty_s),
                                        vcx.mk_local_decl("val", write_ty_out.snapshot),
                                    ],
                                    triggers: vir::bvec![in &vcx.arena;
                                        vcx.mk_func_app(
                                            crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                            &[vcx.mk_func_app(
                                                crate::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                                &[
                                                    vcx.mk_local_ex("self"),
                                                    vcx.mk_local_ex("val"),
                                                ],
                                            )],
                                        ),
                                    ],
                                    body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                        kind: vir::BinOpKind::CmpEq,
                                        lhs: vcx.mk_func_app(
                                            crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                            &[vcx.mk_func_app(
                                                crate::vir_format!(vcx, "{name_s}_write_{write_idx}"),
                                                &[
                                                    vcx.mk_local_ex("self"),
                                                    vcx.mk_local_ex("val"),
                                                ],
                                            )],
                                        ),
                                        rhs: vcx.mk_func_app(
                                            crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                            &[vcx.mk_local_ex("self")],
                                        ),
                                    }))),
                                })))
                            },
                        }));
                    }
                }

                // constructor
                let cons_name = crate::vir_format!(vcx, "{name_s}_cons");
                {
                    let cons_qvars = vir::BumpVec::from_iter_in(
                         field_ty_out.iter()
                            .enumerate()
                            .map(|(idx, field_ty_out)| vcx.mk_local_decl(
                                crate::vir_format!(vcx, "f{idx}"),
                                field_ty_out.snapshot,
                            )),
                        &vcx.arena,
                    );
                    let cons_args = field_ty_out.iter()
                        .enumerate()
                        .map(|(idx, field_ty_out)| vcx.mk_local_ex(
                            crate::vir_format!(vcx, "f{idx}"),
                        ))
                        .collect::<Vec<_>>();
                    let cons_call = vcx.mk_func_app(cons_name, &cons_args);

                    for (read_idx, _) in field_ty_out.iter().enumerate() {
                        axioms.push(vcx.alloc(vir::DomainAxiomData {
                            name: crate::vir_format!(vcx, "ax_{name_s}_cons_read_{read_idx}"),
                            expr: vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                                qvars: cons_qvars.clone(),
                                triggers: vir::bvec![in &vcx.arena;
                                    vcx.mk_func_app(
                                        crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                        &[cons_call],
                                    ),
                                ],
                                body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                    kind: vir::BinOpKind::CmpEq,
                                    lhs: vcx.mk_func_app(
                                        crate::vir_format!(vcx, "{name_s}_read_{read_idx}"),
                                        &[cons_call],
                                    ),
                                    rhs: cons_args[read_idx],
                                }))),
                            }))),
                        }));
                    }

                    let cons_call_with_reads = vcx.mk_func_app(
                        cons_name,
                        &field_ty_out
                            .iter()
                            .enumerate()
                            .map(|(idx, field_ty_out)| vcx.mk_func_app(
                                crate::vir_format!(vcx, "{name_s}_read_{idx}"),
                                &[vcx.mk_local_ex("self")],
                            ))
                            .collect::<Vec<_>>(),
                    );
                    axioms.push(vcx.alloc(vir::DomainAxiomData {
                        name: crate::vir_format!(vcx, "ax_{name_s}_cons"),
                        expr: vcx.alloc(vir::ExprData::Forall(vcx.alloc(vir::ForallData {
                            qvars: vir::bvec![in &vcx.arena;
                                vcx.mk_local_decl("self", ty_s),
                            ],
                            triggers: vir::bvec![in &vcx.arena;
                                cons_call_with_reads,
                            ],
                            body: vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                                kind: vir::BinOpKind::CmpEq,
                                lhs: cons_call_with_reads,
                                rhs: vcx.mk_local_ex("self"),
                            }))),
                        }))),
                    }));
                }

                // predicate
                let predicate = {
                    // TODO: same as above, but with self_s instead of self...
                    let cons_call_with_reads = vcx.mk_func_app(
                        cons_name,
                        &field_ty_out
                            .iter()
                            .enumerate()
                            .map(|(idx, field_ty_out)| vcx.mk_func_app(
                                crate::vir_format!(vcx, "{name_s}_read_{idx}"),
                                &[vcx.mk_local_ex("self_s")],
                            ))
                            .collect::<Vec<_>>(),
                    );
                    let cons_eq = vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                        kind: vir::BinOpKind::CmpEq,
                        lhs: vcx.mk_local_ex("self_s"),
                        rhs: cons_call_with_reads,
                    })));
                    let expr = field_ty_out.iter()
                        .enumerate()
                        .fold(cons_eq, |base, (idx, field_ty_out)| vcx.alloc(vir::ExprData::BinOp(vcx.alloc(vir::BinOpData {
                            kind: vir::BinOpKind::And,
                            lhs: base,
                            rhs: vcx.alloc(vir::ExprData::PredicateApp(vcx.alloc(vir::PredicateAppData {
                                target: field_ty_out.predicate_name,
                                args: vir::bvec![in &vcx.arena;
                                    vcx.mk_func_app(
                                        crate::vir_format!(vcx, "{name_p}_field_{idx}"),
                                        &[vcx.mk_local_ex("self_p")],
                                    ),
                                    vcx.mk_func_app(
                                        crate::vir_format!(vcx, "{name_s}_read_{idx}"),
                                        &[vcx.mk_local_ex("self_s")],
                                    ),
                                ],
                            }))),
                        }))));
                    vcx.alloc(vir::PredicateData {
                        name: name_p,
                        args: vir::bvec![in &vcx.arena;
                            vcx.mk_local_decl("self_p", &vir::TypeData::Ref),
                            vcx.mk_local_decl("self_s", ty_s),
                        ],
                        expr: Some(expr),
                    })
                };

                Ok((TypeEncoderOutput {
                    snapshot: crate::vir_domain! { vcx; domain [name_s] {
                        with_funcs [funcs];
                        with_axioms [axioms];
                    } },
                    predicate,
                    function_unreachable: mk_unreachable(vcx, name_s, ty_s),
                    method_refold: mk_refold(vcx, name_p, ty_s),
                    field_projection_p,
                }, ()))
            }
            _ => Err((TypeEncoderError::UnsupportedType, None)),
        })
    }
}
