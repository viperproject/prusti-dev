use rustc_middle::ty;
use rustc_middle::ty::layout::IntegerExt;
use rustc_target::abi::Integer;
use std::collections::HashMap;
use prusti_common::vir::{self, Expr, FallibleExprFolder, FallibleStmtFolder, Type, PermAmount, EnumVariantIndex};
use crate::encoder::Encoder;
use crate::encoder::errors::{EncodingError, EncodingResult, SpannedEncodingResult, RunIfErr};
use crate::encoder::snapshot::{Snapshot, patcher::SnapshotPatcher};

type PredicateName = String;

/// Encodes MIR types into snapshots, and keeps track of which types have
/// already been encoded.
pub struct SnapshotEncoder {
    /// Types that are currently being encoded. Stores the VIR type that will
    /// be the result of the snapshot operation: either a primitive VIR type,
    /// or an instance of [Type::Snapshot].
    ///
    /// This is necessary to be able to encode recursive types; when encoding
    /// a snapshot where once of the fields is the same type, it is enough to
    /// look up the resulting type from this hashmap.
    in_progress: HashMap<PredicateName, Type>,

    /// Maps predicate names to encoded snapshots.
    encoded: HashMap<PredicateName, Snapshot>,
}

/// Snapshot encoding flattens references and boxes. This function removes any
/// [Box<...>] or reference (mutable or shared) wrappers.
fn strip_refs_and_boxes<'tcx>(ty: ty::Ty<'tcx>) -> ty::Ty<'tcx> {
    match ty.kind() {
        _ if ty.is_box() => strip_refs_and_boxes(ty.boxed_ty()),
        ty::TyKind::Ref(_, ref sub_ty, _) => strip_refs_and_boxes(sub_ty),
        _ => ty,
    }
}

fn strip_refs_and_boxes_expr<'p, 'v: 'p, 'tcx: 'v>(
    encoder: &'p Encoder<'v, 'tcx>,
    ty: ty::Ty<'tcx>,
    expr: Expr,
) -> EncodingResult<(ty::Ty<'tcx>, Expr)> {
    // TODO: fold/unfold fails to add correct unfolding for val_ref (adding it
    // here does not work either), e.g. [cons(self.f$i.val_ref.val_int)]
    // misses the unfolding for [ref$i32].
    match ty.kind() {
        _ if ty.is_box() => strip_refs_and_boxes_expr(
            encoder,
            ty.boxed_ty(),
            Expr::field(
                expr,
                encoder.encode_dereference_field(ty.boxed_ty())?,
            ),
        ),
        ty::TyKind::Ref(_, ref sub_ty, _) => strip_refs_and_boxes_expr(
            encoder,
            sub_ty,
            Expr::field(
                expr,
                encoder.encode_dereference_field(sub_ty)?,
            ),
        ),
        _ => Ok((ty, expr)),
    }
}

// TODO: separate struct for Complex encoding?
impl SnapshotEncoder {
    pub fn new() -> Self {
        Self {
            in_progress: HashMap::new(),
            encoded: HashMap::new(),
        }
    }

    /// Returns a list of Viper functions needed by the encoded snapshots.
    pub fn get_viper_functions(&self) -> Vec<vir::Function> {
        let mut funcs = vec![];
        for snapshot in self.encoded.values() {
            match snapshot {
                Snapshot::Complex { snap_func, .. } => funcs.push(snap_func.clone()),
                _ => {},
            }
        }
        funcs
    }

    /// Returns a list of Viper domains needed by the encoded snapshots.
    pub fn get_viper_domains(&self) -> Vec<vir::Domain> {
        let mut domains = vec![];
        for snapshot in self.encoded.values() {
            match snapshot {
                Snapshot::Complex { domain, .. } => domains.push(domain.clone()),
                _ => {},
            }
        }
        domains
    }

    pub fn patch_snapshots_method<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        method: vir::CfgMethod,
    ) -> EncodingResult<vir::CfgMethod> {
        debug!("[snap] method: {:?}", method.name());
        let mut patcher = SnapshotPatcher {
            snapshot_encoder: self,
            encoder,
        };
        method.patch_statements(|stmt| vir::FallibleStmtFolder::fallible_fold(&mut patcher, stmt))
    }

    pub fn patch_snapshots_function<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        mut function: vir::Function,
    ) -> EncodingResult<vir::Function> {
        debug!("[snap] function: {:?}", function.name);
        let mut patcher = SnapshotPatcher {
            snapshot_encoder: self,
            encoder,
        };
        function.pres = function.pres.into_iter()
            .map(|e| FallibleExprFolder::fallible_fold(&mut patcher, e))
            .collect::<Result<Vec<_>, _>>()?;
        function.posts = function.posts.into_iter()
            .map(|e| FallibleExprFolder::fallible_fold(&mut patcher, e))
            .collect::<Result<Vec<_>, _>>()?;
        if let Some(body) = function.body {
            function.body = Some(FallibleExprFolder::fallible_fold(&mut patcher, body)?);
        }
        Ok(function)
    }

    pub fn patch_snapshots_expr<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        expr: Expr,
    ) -> EncodingResult<Expr> {
        debug!("[snap] expr: {:?}", expr);
        let mut patcher = SnapshotPatcher {
            snapshot_encoder: self,
            encoder,
        };
        FallibleExprFolder::fallible_fold(&mut patcher, expr)
    }

    /// Converts a SnapApp(expr) into an appropriate expression based on the
    /// kind of this snapshot.
    pub(super) fn snap_app<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        expr: Expr,
    ) -> EncodingResult<Expr> {
        match expr.get_type() {
            vir::Type::TypedRef(ref name) => {
                let ty = encoder.decode_type_predicate(name)?;
                let (ty, expr) = strip_refs_and_boxes_expr(encoder, ty, expr)?;
                // TODO: move to snapshot mod?
                // TODO: unfolding might not be necessary?
                Ok(match ty.kind() {
                    ty::TyKind::Int(_)
                    | ty::TyKind::Uint(_)
                    | ty::TyKind::Char => Expr::wrap_in_unfolding(
                        expr.clone(),
                        Expr::field(
                            expr.clone(),
                            vir::Field::new("val_int", Type::Int)
                        ),
                    ),
                    ty::TyKind::Bool => Expr::wrap_in_unfolding(
                        expr.clone(),
                        Expr::field(
                            expr.clone(),
                            vir::Field::new("val_bool", Type::Bool)
                        ),
                    ),
                    ty::TyKind::Tuple(substs) if substs.is_empty() => 0.into(),
                    ty::TyKind::Adt(adt_def, _) if adt_def.variants.is_empty() => 0.into(),
                    ty::TyKind::Adt(adt_def, _) if adt_def.variants.len() == 1 && adt_def.variants[rustc_target::abi::VariantIdx::from_u32(0)].fields.is_empty() => 0.into(),
                    ty::TyKind::Param(_) => 0.into(),
                    _ => {
                        let snapshot = self.encode_snapshot(encoder, ty)?;
                        Expr::func_app(
                            "snap$".to_string(),
                            vec![expr.clone()],
                            vec![vir::LocalVar::new("_", expr.get_type().clone())],
                            snapshot.get_type(),
                            vir::Position::default(),
                        )
                    }
                })
            }
            _ => unreachable!("invalid SnapApp"), // TODO: proper error
        }
    }

    /// Converts field access on a snapshot to a domain function call.
    pub(super) fn snap_field<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        expr: Expr,
        field: vir::Field,
    ) -> EncodingResult<Expr> {
        match expr.get_type() {
            Type::Snapshot(ref name) => {
                let ty = encoder.decode_type_predicate(name)?;
                let snapshot = self.encode_snapshot(encoder, ty)?;
                match snapshot {
                    Snapshot::Complex { variants, .. } => {
                        println!("want field: {:?}, have fields: {:?}", field, variants);
                        Ok(Expr::domain_func_app(
                            // TODO: fields of enum variants
                            // -> add SnapshotVariant to vir::Type ?
                            variants[0].get(&field.name).unwrap().clone(),
                            vec![expr],
                        ))
                    },
                    _ => unreachable!("invalid snapshot field (not Complex)"),
                }
            }
            _ => unreachable!("invalid snapshot field"),
        }
    }

    pub fn supports_equality<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<bool> {
        let snapshot = self.encode_snapshot(encoder, ty)?;
        Ok(snapshot.supports_equality())
    }

    pub fn encode_type<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<Type> {
        print!("snapshot type of {:?} will be ", ty);
        let ty = strip_refs_and_boxes(ty);
        let predicate_name = encoder.encode_type_predicate_use(ty)?;
        let ret = match ty.kind() {
            ty::TyKind::Int(_) => Type::Int,
            ty::TyKind::Uint(_) => Type::Int,
            ty::TyKind::Char => Type::Int,
            ty::TyKind::Bool => Type::Bool,
            ty::TyKind::Tuple(substs) if substs.is_empty() => Type::Int,
            ty::TyKind::Adt(adt_def, _) if adt_def.variants.is_empty() => Type::Int,
            ty::TyKind::Adt(adt_def, _) if adt_def.variants.len() == 1 && adt_def.variants[rustc_target::abi::VariantIdx::from_u32(0)].fields.is_empty() => Type::Int,
            ty::TyKind::Param(_) => Type::Int,
            _ => Type::Snapshot(predicate_name.to_string()),
        };
        println!("{:?}", ret);
        Ok(ret)
    }

    fn encode_snapshot<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<Snapshot> {
        println!("encode snapshot of {:?}", ty);
        let ty = strip_refs_and_boxes(ty);
        let predicate_name = encoder.encode_type_predicate_use(ty)?;

        // was the snapshot for the type already encoded?
        if let Some(snapshot) = self.encoded.get(&predicate_name) {
            return Ok((*snapshot).clone()); // TODO: can we not clone?
        }

        // is the snapshot currently being encoded? (handle recursive data types)
        if let Some(ty) = self.in_progress.get(&predicate_name) {
            // TODO: can this actually happen?
            unimplemented!("Lazy?");
            // return Ok(ty.clone());
        }

        // otherwise, encode

        // figure out resulting type
        let snapshot_type = self.encode_type(encoder, ty)?;

        // record in-progress encoding
        self.in_progress.insert(predicate_name.to_string(), snapshot_type.clone());

        // encode snapshot
        let snapshot = self.encode_snapshot_internal(encoder, ty, &predicate_name)
            // TODO: clean up?
            /*.run_if_err(|| {
                self.in_progress.remove(&predicate_name);
            })*/
            ?;

        // remove in-progress encoding
        self.in_progress.remove(&predicate_name);

        // remember resulting snapshot
        assert_eq!(snapshot_type, snapshot.get_type());
        self.encoded.insert(predicate_name.to_string(), snapshot.clone());

        // TODO: resolve Lazy(..) ?
        Ok(snapshot)
    }

    fn encode_snapshot_internal<'p, 'v: 'p, 'tcx: 'v>(
        &mut self,
        encoder: &'p Encoder<'v, 'tcx>,
        ty: ty::Ty<'tcx>,
        predicate_name: &str,
    ) -> EncodingResult<Snapshot> {
        let tcx = encoder.env().tcx();
        let predicate = encoder.encode_type_predicate_def(ty)?;

        let arg_self = vir::LocalVar::new(
            "self",
            Type::TypedRef(predicate_name.to_string()),
        );
        let arg_expr = Expr::local(arg_self);

        match ty.kind() {
            // strip refs and boxes
            // the result is a Lazy snapshot (resolved later) to ensure that
            // recursive types do not cause infinite encoding loops
            // TODO: since all calls go through encode_type, this may not be needed at all
            _ if ty.is_box() => Ok(Snapshot::Lazy(self.encode_type(encoder, ty)?)),
            ty::TyKind::Ref(_, _, _) => Ok(Snapshot::Lazy(self.encode_type(encoder, ty)?)),

            ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Char => Ok(Snapshot::Primitive(Type::Int)),
            ty::TyKind::Bool => Ok(Snapshot::Primitive(Type::Bool)),

            ty::TyKind::Param(_) => Ok(Snapshot::Abstract),

            // TODO: closures, never type

            ty::TyKind::Tuple(substs) => {
                let mut fields = vec![];
                for (field_num, field_ty) in substs.iter().enumerate() {
                    let field_name = format!("tuple_{}", field_num);
                    let field_ty = field_ty.expect_ty(); // why not use substs?
                    fields.push(SnapshotField {
                        name: field_name.to_string(),
                        access: self.snap_app(encoder, Expr::field(
                            arg_expr.clone(),
                            encoder.encode_raw_ref_field(field_name.to_string(), field_ty)?,
                        ))?,
                        typ: self.encode_type(encoder, field_ty)?,
                    });
                }
                self.encode_complex(encoder, vec![SnapshotVariant {
                    discriminant: -1,
                    fields,
                }], predicate, predicate_name)
            }
            ty::TyKind::Adt(adt_def, subst) if adt_def.is_struct() => {
                let mut fields = vec![];
                for field in adt_def.all_fields() { // or adt_def.variants[0].fields ?
                    let field_ty = field.ty(tcx, subst);
                    fields.push(SnapshotField {
                        name: format!("f${}", field.ident),
                        access: self.snap_app(encoder, Expr::field(
                            arg_expr.clone(),
                            encoder.encode_struct_field(&field.ident.to_string(), field_ty)?,
                        ))?,
                        typ: self.encode_type(encoder, field_ty)?,
                    });
                }
                self.encode_complex(encoder, vec![SnapshotVariant {
                    discriminant: -1,
                    fields,
                }], predicate, predicate_name)
            }
            ty::TyKind::Adt(adt_def, subst) if adt_def.is_enum() => {
                let mut variants = vec![];
                for (variant_idx, variant) in adt_def.variants.iter_enumerated() {
                    let mut fields = vec![];
                    let variant_idx: usize = variant_idx.into();
                    for field in &variant.fields {
                        let field_ty = field.ty(tcx, subst);
                        fields.push(SnapshotField {
                            name: format!("f${}", field.ident),
                            access: self.snap_app(encoder, Expr::field(
                                match predicate {
                                    vir::Predicate::Enum(ref enum_predicate) => {
                                        let (_, ref variant_name, _) = enum_predicate.variants[variant_idx];
                                        arg_expr.clone().variant(variant_name)
                                    }
                                    vir::Predicate::Struct(..) => {
                                        arg_expr.clone()
                                    }
                                    _ => unreachable!(),
                                },
                                encoder.encode_struct_field(&field.ident.to_string(), field_ty)?,
                            ))?,
                            typ: self.encode_type(encoder, field_ty)?,
                        });
                    }

                    let discriminant_raw = adt_def.discriminant_for_variant(
                        tcx,
                        rustc_target::abi::VariantIdx::from_usize(variant_idx)
                    ).val;
                    let size = ty::tls::with(|tcx| Integer::from_attr(&tcx, adt_def.repr.discr_type()).size());
                    let discriminant = size.sign_extend(discriminant_raw) as i128;
                    variants.push(SnapshotVariant {
                        discriminant,
                        fields,
                    });
                }
                self.encode_complex(encoder, variants, predicate, predicate_name)
            }

            // TODO: Abstract ?
            x => Err(EncodingError::unsupported(format!("{:?}", x)))
        }
    }

    /// Encodes the snapshot for a complex data structure (tuple, struct,
    /// enum, or closure). There may be zero or more variants, each with zero
    /// or more fields to encode. The returned snapshot will be of the
    /// [Snapshot::Complex] variant, except for empty enums and structs that
    /// can be represented with [Snapshot::Unit].
    fn encode_complex<'p, 'v: 'p, 'tcx: 'v>(
        &self,
        encoder: &'p Encoder<'v, 'tcx>,
        variants: Vec<SnapshotVariant>,
        predicate: vir::Predicate,
        predicate_name: &str,
    ) -> EncodingResult<Snapshot> {
        if variants.is_empty()
            || (variants.len() == 1 && variants[0].fields.len() == 0) {
            return Ok(Snapshot::Unit);
        }

        let domain_name = format!("Snap${}", predicate_name);
        let snapshot_type = Type::Snapshot(predicate_name.to_string());
        let mut domain_funcs = vec![];
        let mut domain_axioms = vec![];
        let mut variant_field_funcs = vec![];
        let mut variant_snap_bodies = vec![];

        let arg_ref_local = vir::LocalVar::new(
            "self",
            Type::TypedRef(predicate_name.to_string()),
        );
        let arg_ref_expr = Expr::local(arg_ref_local.clone());

        // encode discriminant function
        // TODO: only if multiple variants
        let arg = vir::LocalVar::new("self", snapshot_type.clone());
        let discriminant_func = vir::DomainFunc {
            name: "variant$".to_string(),
            formal_args: vec![vir::LocalVar::new(
                "self",
                snapshot_type.clone(),
            )],
            return_type: Type::Int,
            unique: false,
            domain_name: domain_name.to_string(),
        };
        domain_funcs.push(discriminant_func.clone());

        // for each variant, we need to encode.
        // * the constructor, which takes the flattened value-only
        //   representation of the variant and returns an instance of the
        //   snapshot domain
        // * the injectivity axiom for that constructor:
        //   ```plain
        //   forall _l_args..., _r_args... :: {cons(_l_args...), cons(_r_args)}
        //     cons(_l_args...) == cons(_r_args) ==> _l_args... == _r_args...
        //   ```
        // * the discriminant axiom for that constructor:
        //   ```plain
        //   discriminant(cons<N>(...)) == N
        //   ```
        // * for each field in the variant:
        //   * field access function
        //   * field access axiom:
        //     ```plain
        //     forall args... :: {field(cons(arg_field, other_args...))}
        //       field(cons(arg_field, other_args...)) == arg_field
        //     ```
        for (variant_idx, variant) in variants.iter().enumerate() {
            let constructor_name = format!("cons${}$", variant_idx);
            let args = variant.fields.iter()
                .enumerate()
                .map(|(idx, field)| vir::LocalVar::new(
                    format!("_{}", idx),
                    field.typ.clone(),
                )).collect::<Vec<vir::LocalVar>>();
            // TODO: filter out Units

            // encode constructor
            let constructor = vir::DomainFunc {
                name: constructor_name.to_string(),
                formal_args: args.clone(),
                return_type: snapshot_type.clone(),
                unique: false,
                domain_name: domain_name.to_string(),
            };
            domain_funcs.push(constructor.clone());

            let encode_prefixed_args = |prefix: &str| -> Vec<vir::LocalVar> {
                args.iter().map(|arg| vir::LocalVar::new(
                        format!("{}{}", prefix, arg.name),
                        arg.typ.clone(),
                    )).collect()
            };
            let encode_constructor_call = |args: &Vec<vir::LocalVar>| -> Expr {
                Expr::domain_func_app(
                    constructor.clone(),
                    args.iter().cloned().map(Expr::local).collect(),
                )
            };

            // encode injectivity axiom of constructor
            domain_axioms.push({
                let lhs_args = encode_prefixed_args("_l");
                let rhs_args = encode_prefixed_args("_r");

                let lhs_call = encode_constructor_call(&lhs_args);
                let rhs_call = encode_constructor_call(&rhs_args);

                let mut forall_vars = vec![];
                forall_vars.extend(lhs_args.iter().cloned());
                forall_vars.extend(rhs_args.iter().cloned());

                let conjunction = vir::ExprIterator::conjoin(
                    &mut lhs_args.into_iter().zip(rhs_args.into_iter()).map( // .iter().cloned() also?
                        |(l, r)| Expr::eq_cmp(
                            Expr::local(l.clone()),
                            Expr::local(r.clone()),
                        )
                    ) // .conjoin() ...
                );

                vir::DomainAxiom {
                    // TODO: why domain_name in name?
                    name: format!("{}${}$injectivity", domain_name, variant_idx),
                    expr: Expr::forall(
                        forall_vars,
                        vec![vir::Trigger::new(vec![lhs_call.clone(), rhs_call.clone()])],
                        Expr::implies(
                            Expr::eq_cmp(lhs_call, rhs_call),
                            conjunction
                        )
                    ),
                    domain_name: domain_name.to_string(),
                }
            });

            // encode discriminant axiom
            domain_axioms.push({
                let args = encode_prefixed_args("");
                let call = encode_constructor_call(&args);
                vir::DomainAxiom {
                    // TODO: why domain_name in name?
                    name: format!("{}${}$discriminant_axiom", domain_name, variant_idx),
                    expr: Expr::forall(
                        args.iter().cloned().collect(),
                        vec![vir::Trigger::new(vec![
                            call.clone()
                        ])],
                        Expr::eq_cmp(
                            Expr::domain_func_app(
                                discriminant_func.clone(),
                                vec![call.clone()],
                            ),
                            variant_idx.into(),
                        ),
                    ),
                    domain_name: domain_name.to_string(),
                }
            });

            let mut field_access_funcs = HashMap::new();

            for (field_idx, field) in variant.fields.iter().enumerate() {
                // encode field access function
                let field_access_func = vir::DomainFunc {
                    // TODO: why domain_name in name?
                    name: format!("{}${}$field${}", domain_name, variant_idx, field.name),
                    formal_args: vec![vir::LocalVar::new(
                        "self",
                        snapshot_type.clone(),
                    )],
                    return_type: field.typ.clone(),
                    unique: false,
                    domain_name: domain_name.to_string(),
                };
                domain_funcs.push(field_access_func.clone());
                field_access_funcs.insert(field.name.to_string(), field_access_func.clone());

                // encode field access axiom
                domain_axioms.push({
                    let args = encode_prefixed_args("");
                    let call = encode_constructor_call(&args);
                    let field_of_cons = Expr::domain_func_app(
                        field_access_func.clone(),
                        vec![call.clone()],
                    );
                    vir::DomainAxiom {
                        // TODO: why domain_name in name?
                        name: format!("{}${}$field${}$axiom", domain_name, variant_idx, field.name),
                        expr: Expr::forall(
                            args.clone(),
                            vec![vir::Trigger::new(vec![
                                field_of_cons.clone()
                            ])],
                            Expr::eq_cmp(
                                field_of_cons.clone(),
                                Expr::local(args[field_idx].clone()),
                            ),
                        ),
                        domain_name: domain_name.to_string(),
                    }
                });
            }

            variant_field_funcs.push(field_access_funcs);

            // encode constructor call for this variant
            let mut snap_body = Expr::domain_func_app(
                constructor.clone(),
                variant.fields.iter()
                    .map(|f| f.access.clone())
                    .collect(),
            );
            if !variant.fields.is_empty() {
                snap_body = self.unfolding_enum_variant(
                    arg_ref_expr.clone(),
                    snap_body,
                    &predicate,
                    predicate_name,
                    variant_idx,
                )?;
            }
            variant_snap_bodies.push(snap_body);
        }

        // encode snap function
        let snap_func = {
            // <discriminant> == <discriminant of variant 0>
            //   ? cons0(fields_of_variant_0...)
            //   : ...

            // TODO: avoid clone somehow?
            let mut body = variant_snap_bodies[0].clone();
            for i in 1..variants.len() {
                body = Expr::ite(
                    Expr::eq_cmp(
                        Expr::field(
                            arg_ref_expr.clone(),
                            encoder.encode_discriminant_field(),
                        ),
                        variants[i].discriminant.into(),
                    ),
                    variant_snap_bodies[i].clone(),
                    body,
                );
            }

            vir::Function {
                name: "snap$".to_string(),
                formal_args: vec![arg_ref_local.clone()],
                return_type: snapshot_type.clone(),
                pres: vec![Expr::predicate_access_predicate(
                    predicate_name.clone(),
                    arg_ref_expr.clone(),
                    PermAmount::Read,
                )],
                posts: vec![], // TODO: with optimisations there should be a post ...
                body: Some(Expr::wrap_in_unfolding(
                    arg_ref_expr.clone(),
                    body,
                )),
            }
        };

        // create domain
        let domain = vir::Domain {
            name: domain_name,
            functions: domain_funcs,
            axioms: domain_axioms,
            type_vars: vec![],
        };

        Ok(Snapshot::Complex {
            predicate_name: predicate_name.to_string(),
            domain,
            snap_func,
            variants: variant_field_funcs,
        })
    }

    fn unfolding_enum_variant(
        &self,
        expr_self: Expr,
        expr_call: Expr,
        predicate: &vir::Predicate,
        predicate_name: &str,
        variant_idx: usize,
    ) -> EncodingResult<Expr> {
        // TODO: why is this not generated by fold/unfold automatically?
        match predicate {
            vir::Predicate::Enum(enum_predicate) => {
                let (_, ref variant_name, _) = enum_predicate.variants[variant_idx];
                Ok(Expr::unfolding(
                    format!("{}{}", predicate_name, variant_name),
                    vec![expr_self.variant(variant_name)],
                    expr_call,
                    vir::PermAmount::Read,
                    Some(EnumVariantIndex::new(variant_name.to_string())),
                ))
            }
            vir::Predicate::Struct(_) => {
                debug_assert_eq!(variant_idx, 0);
                Ok(Expr::unfolding(
                    predicate_name.to_string(),
                    vec![expr_self.clone()],
                    expr_call,
                    vir::PermAmount::Read,
                    None,
                ))
            }
            _ => {
                Err(EncodingError::incorrect(
                    "predicate does not correspond to an enum or struct".to_string()
                ))
            }
        }
    }
}

struct SnapshotVariant {
    discriminant: i128, // TODO: Option<i128> ?
    fields: Vec<SnapshotField>,
}

struct SnapshotField {
    name: String,
    access: Expr, // _ARG(.field)*
    typ: Type,
}
