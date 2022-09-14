// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use ::log::{info, debug};
use prusti_common::utils::identifiers::encode_identifier;
use vir_crate::common::check_mode::CheckMode;
use crate::encoder::builtin_encoder::BuiltinEncoder;
use crate::encoder::builtin_encoder::BuiltinMethodKind;
use crate::encoder::errors::{ErrorManager, SpannedEncodingError, EncodingError};
use crate::encoder::foldunfold;
use crate::encoder::procedure_encoder::ProcedureEncoder;
use crate::error_unsupported;
use prusti_common::{vir_expr, vir_local};
use prusti_common::config;
use prusti_common::report::log;
use prusti_interface::data::ProcedureDefId;
use prusti_interface::environment::Environment;
use prusti_interface::specs::typed;
use prusti_interface::PrustiError;
use vir_crate::polymorphic::{self as vir};
use vir_crate::common::identifier::WithIdentifier;
use prusti_rustc_interface::hir::def_id::DefId;
use prusti_rustc_interface::middle::mir;
use prusti_rustc_interface::middle::ty;
use std::cell::{Cell, RefCell, RefMut, Ref};
use std::fmt::Debug;
use rustc_hash::{FxHashSet, FxHashMap};
use std::io::Write;
use std::rc::Rc;
use crate::encoder::stub_procedure_encoder::StubProcedureEncoder;
use std::ops::AddAssign;
use prusti_interface::specs::typed::ProcedureSpecificationKind;
use crate::encoder::name_interner::NameInterner;
use crate::encoder::errors::EncodingResult;
use crate::encoder::errors::SpannedEncodingResult;
use crate::encoder::mirror_function_encoder::MirrorEncoder;
use crate::encoder::snapshot::interface::{SnapshotEncoderInterface, SnapshotEncoderState};
use crate::encoder::purifier;
use super::builtin_encoder::BuiltinDomainKind;
use super::high::builtin_functions::HighBuiltinFunctionEncoderState;
use super::middle::core_proof::{MidCoreProofEncoderState, MidCoreProofEncoderInterface};
use super::mir::{
    sequences::{
        MirSequencesEncoderState, MirSequencesEncoderInterface,
    },
    contracts::ContractsEncoderState,
    procedures::MirProcedureEncoderState,
    type_invariants::TypeInvariantEncoderState,
    pure::{
        PureFunctionEncoderState, PureFunctionEncoderInterface,
    },
    types::{
        compute_discriminant_bounds,
        MirTypeEncoderState, MirTypeEncoderInterface,
    },
    specifications::{
        SpecificationsState, SpecificationsInterface,
    }
};
use super::high::types::{HighTypeEncoderState, HighTypeEncoderInterface};
use super::counterexamples::{MirProcedureMappingInterface, MirProcedureMapping};
use super::counterexamples::DiscriminantsState;
use super::high::to_typed::types::HighToTypedTypeEncoderState;

pub struct Encoder<'v, 'tcx: 'v> {
    env: &'v Environment<'tcx>,
    error_manager: RefCell<ErrorManager<'tcx>>,
    /// A map containing all functions: identifier → function definition.
    functions: RefCell<FxHashMap<vir::FunctionIdentifier, Rc<vir::Function>>>,
    builtin_domains: RefCell<FxHashMap<BuiltinDomainKind, vir::Domain>>,
    builtin_domains_in_progress: RefCell<FxHashSet<BuiltinDomainKind>>,
    builtin_methods: RefCell<FxHashMap<BuiltinMethodKind, vir::BodylessMethod>>,
    pub(super) high_builtin_function_encoder_state: HighBuiltinFunctionEncoderState,
    procedures: RefCell<FxHashMap<ProcedureDefId, vir::CfgMethod>>,
    programs: Vec<vir::Program>,
    pub(super) mir_sequences_encoder_state: MirSequencesEncoderState<'tcx>,
    pub(super) contracts_encoder_state: ContractsEncoderState<'tcx>,
    pub(super) mir_procedure_encoder_state: MirProcedureEncoderState,
    pub(super) mid_core_proof_encoder_state: MidCoreProofEncoderState,
    pub(super) mir_type_encoder_state: MirTypeEncoderState<'tcx>,
    pub(super) type_invariant_encoder_state: TypeInvariantEncoderState<'tcx>,
    pub(super) high_type_encoder_state: HighTypeEncoderState<'tcx>,
    pub(super) pure_function_encoder_state: PureFunctionEncoderState<'v, 'tcx>,
    pub(super) typed_type_encoder_state: HighToTypedTypeEncoderState,
    pub(super) specifications_state: SpecificationsState<'tcx>,
    type_discriminant_funcs: RefCell<FxHashMap<String, vir::FunctionIdentifier>>,
    type_cast_functions: RefCell<FxHashMap<(ty::Ty<'tcx>, ty::Ty<'tcx>), vir::FunctionIdentifier>>,
    pub(super) snapshot_encoder_state: SnapshotEncoderState,
    pub(super) mirror_encoder: RefCell<MirrorEncoder>,
    encoding_queue: RefCell<Vec<EncodingTask<'tcx>>>,
    queued_types: RefCell<FxHashSet<ty::Ty<'tcx>>>,
    vir_program_before_foldunfold_writer: Option<RefCell<Box<dyn Write>>>,
    vir_program_before_viper_writer: Option<RefCell<Box<dyn Write>>>,
    encoding_errors_counter: RefCell<usize>,
    name_interner: RefCell<NameInterner>,
    /// Maps locals to the local of their discriminant.
    pub(super) discriminants_state: DiscriminantsState,
    pub(super) mir_procedure_mapping: MirProcedureMapping,
    /// Whether the current pure expression that's being encoded sits inside a trigger closure.
    /// Viper limits the type of expressions that are allowed in quantifier triggers and
    /// this requires special care when encoding array/slice accesses which may come with
    /// bound checks included in the MIR.
    pub(super) is_encoding_trigger: Cell<bool>,
}

pub enum EncodingTask<'tcx> {
    Procedure {
        def_id: ProcedureDefId,
        substs: Vec<(ty::Ty<'tcx>, ty::Ty<'tcx>)>,
    },
    Type {
        ty: ty::Ty<'tcx>,
    },
}

// If the field name is an identifier, removing the leading prefix r#
pub fn encode_field_name(field_name: &str) -> String {
   format!("f${}", field_name.trim_start_matches("r#"))
}

impl<'v, 'tcx> Encoder<'v, 'tcx> {
    pub fn new(
        env: &'v Environment<'tcx>,
        def_spec: typed::DefSpecificationMap,
    ) -> Self {
        let source_path = env.name.source_path();
        let source_filename = source_path.file_name().unwrap().to_str().unwrap();
        let vir_program_before_foldunfold_writer = config::dump_debug_info().then_some(()).map(|_|
            RefCell::new(
                log::build_writer(
                    "vir_program_before_foldunfold",
                    format!("{source_filename}.vir"),
                )
                .ok()
                .unwrap(),
            )
        );
        let vir_program_before_viper_writer = config::dump_debug_info().then_some(()).map(|_|
            RefCell::new(
                log::build_writer(
                    "vir_program_before_viper",
                    format!("{source_filename}.vir"),
                )
                    .ok()
                    .unwrap(),
            )
        );

        Encoder {
            env,
            error_manager: RefCell::new(ErrorManager::new(env.query.codemap())),
            functions: RefCell::new(FxHashMap::default()),
            builtin_domains: RefCell::new(FxHashMap::default()),
            builtin_domains_in_progress: RefCell::new(FxHashSet::default()),
            builtin_methods: RefCell::new(FxHashMap::default()),
            high_builtin_function_encoder_state: Default::default(),
            programs: Vec::new(),
            mir_sequences_encoder_state: Default::default(),
            mir_procedure_encoder_state: Default::default(),
            mid_core_proof_encoder_state: Default::default(),
            procedures: RefCell::new(FxHashMap::default()),
            contracts_encoder_state: Default::default(),
            mir_type_encoder_state: Default::default(),
            type_invariant_encoder_state: Default::default(),
            high_type_encoder_state: Default::default(),
            pure_function_encoder_state: Default::default(),
            typed_type_encoder_state: Default::default(),
            type_discriminant_funcs: RefCell::new(FxHashMap::default()),
            type_cast_functions: RefCell::new(FxHashMap::default()),
            encoding_queue: RefCell::new(vec![]),
            queued_types: Default::default(),
            vir_program_before_foldunfold_writer,
            vir_program_before_viper_writer,
            snapshot_encoder_state: Default::default(),
            mirror_encoder: RefCell::new(MirrorEncoder::new()),
            encoding_errors_counter: RefCell::new(0),
            name_interner: RefCell::new(NameInterner::new()),
            is_encoding_trigger: Cell::new(false),
            specifications_state: SpecificationsState::new(def_spec),
            mir_procedure_mapping: Default::default(),
            discriminants_state: Default::default(),
        }
    }

    pub fn log_vir_program_before_foldunfold<S: ToString>(&self, program: S) {
        if let Some(shared_writer) = &self.vir_program_before_foldunfold_writer {
            let mut writer = shared_writer.borrow_mut();
            writer
                .write_all(program.to_string().as_bytes())
                .ok()
                .unwrap();
            writer
                .write_all("\n\n".to_string().as_bytes())
                .ok()
                .unwrap();
            writer.flush().ok().unwrap();
        }
    }

    pub fn log_vir_program_before_viper<S: ToString>(&self, program: S) {
        if let Some(shared_writer) = &self.vir_program_before_viper_writer {
            let mut writer = shared_writer.borrow_mut();
            writer
                .write_all(program.to_string().as_bytes())
                .ok()
                .unwrap();
            writer
                .write_all("\n\n".to_string().as_bytes())
                .ok()
                .unwrap();
            writer.flush().ok().unwrap();
        }
    }

    #[tracing::instrument(name = "Encoder::initialize", level = "debug", skip(self))]
    fn initialize(&mut self) -> EncodingResult<()> {
        // These are used in optimization passes
        self.encode_builtin_method_def(BuiltinMethodKind::HavocBool)?;
        self.encode_builtin_method_def(BuiltinMethodKind::HavocInt)?;
        self.encode_builtin_method_def(BuiltinMethodKind::HavocRef)?;
        Ok(())
    }

    pub fn env(&self) -> &'v Environment<'tcx> {
        self.env
    }

    pub fn error_manager(&self) -> RefMut<ErrorManager<'tcx>> {
        self.error_manager.borrow_mut()
    }

    pub fn finalize_viper_program(&self, name: String, proc_def_id: DefId) -> SpannedEncodingResult<vir::Program> {
        let error_span = self.env.query.get_def_span(proc_def_id);
        super::definition_collector::collect_definitions(error_span, self, name, self.get_used_viper_methods())
    }

    pub fn get_viper_programs(&mut self) -> Vec<vir::Program> {
        std::mem::take(&mut self.programs)
    }

    pub fn get_core_proof_programs(&mut self) -> Vec<prusti_common::vir::program::Program> {
        if config::counterexample() && config::unsafe_core_proof(){
            self.take_core_proof_programs().into_iter().map(
                |( def_id, program )| {
                    if let Some(def_id) = def_id {
                        self.add_mapping(def_id, &program);
                    }
                    prusti_common::vir::program::Program::Low(program)
            }).collect()
        } else {
            self.take_core_proof_programs().into_iter().map(
                |(_, program)| {
                    prusti_common::vir::program::Program::Low(program)
                }).collect()
        }
    }

    #[tracing::instrument(level = "debug", skip(self))]
    pub(in crate::encoder) fn register_encoding_error(&self, encoding_error: SpannedEncodingError) {
        let prusti_error: PrustiError = encoding_error.into();
        if prusti_error.is_error() {
            self.encoding_errors_counter.borrow_mut().add_assign(1);
        }
        prusti_error.emit(&self.env.diagnostic);
    }

    pub fn count_encoding_errors(&self) -> usize {
        *self.encoding_errors_counter.borrow()
    }

    pub(super) fn get_mirror_domain(&self) -> Option<vir::Domain> {
        self.mirror_encoder.borrow().get_domain().cloned()
    }

    pub(super) fn get_encoded_builtin_domains(&self) -> Vec<vir::Domain> {
        self.builtin_domains.borrow().values().cloned().collect()
    }

    pub(super) fn insert_function(&self, function: vir::Function) -> vir::FunctionIdentifier {
        let identifier: vir::FunctionIdentifier = function.get_identifier().into();
        assert!(self.functions.borrow_mut().insert(identifier.clone(), Rc::new(function)).is_none(), "{identifier:?} is not unique");
        identifier
    }

    pub(super) fn get_function(&self, identifier: &vir::FunctionIdentifier) -> SpannedEncodingResult<Rc<vir::Function>> {
        self.ensure_pure_function_encoded(identifier)?;
        if self.functions.borrow().contains_key(identifier) {
            let map = self.functions.borrow();
            Ok(map[identifier].clone())
        } else if self.contains_snapshot_function(identifier) {
            Ok(self.get_snapshot_function(identifier))
        } else {
            unreachable!("Not found function: {:?}", identifier)
        }
    }

    pub(super) fn get_builtin_methods(
        &self
    ) -> Ref<'_, FxHashMap<BuiltinMethodKind, vir::BodylessMethod>> {
        self.builtin_methods.borrow()
    }

    fn get_used_viper_methods(&self) -> Vec<vir::CfgMethod> {
        self.procedures.borrow_mut().drain().map(|(_, value)| value).collect()
    }

    /// Invoke const evaluation to extract scalar value.
    fn uneval_eval_intlike(
        &self,
        ct: mir::UnevaluatedConst<'tcx>,
    ) -> Option<mir::interpret::Scalar> {
        let tcx = self.env.tcx();
        let param_env = tcx.param_env(ct.def.did);
        tcx.const_eval_resolve(param_env, ct, None)
            .ok()
            .and_then(|const_value| const_value.try_to_scalar())
    }

    /// Extract scalar value, invoking const evaluation if necessary.
    pub fn const_eval_intlike(
        &self,
        value: mir::ConstantKind<'tcx>,
    ) -> EncodingResult<mir::interpret::Scalar> {
        let opt_scalar_value = match value {
            mir::ConstantKind::Ty(value) => match value.kind() {
                ty::ConstKind::Value(ref const_value) => {
                    const_value.try_to_scalar()
                }
                ty::ConstKind::Unevaluated(ct) => {
                    let mir_ct = mir::UnevaluatedConst::new(ct.def, ct.substs);
                    self.uneval_eval_intlike(mir_ct)
                },
                _ => error_unsupported!("unsupported const kind: {:?}", value),
            }
            mir::ConstantKind::Val(val, _) => val.try_to_scalar(),
            mir::ConstantKind::Unevaluated(ct, _) => self.uneval_eval_intlike(ct),
        };
        opt_scalar_value.ok_or_else(|| EncodingError::unsupported(format!("unsupported constant value: {value:?}")))
    }

    /// Encodes a value in a field if the base expression is a reference or
    /// a primitive types.
    /// For composed data structures, the base expression is returned.
    pub fn encode_value_expr(&self, base: vir::Expr, ty: ty::Ty<'tcx>) -> EncodingResult<vir::Expr> {
        match ty.kind() {
            ty::TyKind::Adt(_, _)
            | ty::TyKind::Closure(_, _)
            | ty::TyKind::Array(..)
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Param(_) => {
                Ok(base) // don't use a field for tuples and ADTs
            }
            _ => {
                let value_field = self.encode_value_field(ty)?;
                let pos = base.pos();
                Ok(base.field(value_field).set_pos(pos))
            }
        }
    }

    pub fn encode_dereference_field(&self, ty: ty::Ty<'tcx>)
    -> EncodingResult<vir::Field>
    {
        self.encode_raw_ref_field("val_ref".to_string(), ty)
    }

    pub fn encode_struct_field(&self, field_name: &str, ty: ty::Ty<'tcx>)
    -> EncodingResult<vir::Field>
    {
        self.encode_raw_ref_field(encode_field_name(field_name), ty)
    }

    pub fn encode_discriminant_func_app(
        &self,
        place: vir::Expr,
        adt_def: ty::AdtDef<'tcx>,
    ) -> SpannedEncodingResult<vir::Expr> {
        let typ = place.get_type().clone();
        let mut name = typ.name();
        name.push_str("$$discriminant$$");
        let self_local_var = vir_local!{ self: {typ.clone()} };
        if !self.type_discriminant_funcs.borrow().contains_key(&name) {
            let precondition = vir::Expr::predicate_access_predicate(
                typ,
                self_local_var.clone().into(),
                vir::PermAmount::Read
            );
            let result = vir_local!{ __result: Int };
            let postcondition = compute_discriminant_bounds(
                adt_def, self.env.tcx(), &result.clone().into());

            let discr_field = self.encode_discriminant_field();
            let self_local_var_expr: vir::Expr = self_local_var.clone().into();
            let function = vir::Function {
                name: name.clone(),
                type_arguments: Vec::new(),
                formal_args: vec![self_local_var.clone()],
                return_type: vir::Type::Int,
                pres: vec![precondition],
                posts: vec![
                    postcondition,
                    self.encode_discriminant_postcondition(
                        self_local_var_expr.clone(),
                        vir::Expr::local(result),
                    ).unwrap(), // TODO: no unwrap
                ],
                body: Some(self_local_var_expr.field(discr_field)),
            };

            self.log_vir_program_before_foldunfold(function.to_string());

            let final_function = foldunfold::add_folding_unfolding_to_function(
                function,
                self.get_used_viper_predicates_map()?,
            );
            let identifier = self.insert_function(final_function.unwrap());
            self.type_discriminant_funcs.borrow_mut().insert(name.clone(), identifier);
        }
        Ok(vir::Expr::FuncApp( vir::FuncApp {
            function_name: name,
            type_arguments: Vec::new(),
            arguments: vec![place],
            formal_arguments: vec![self_local_var],
            return_type: vir::Type::Int,
            position: vir::Position::default(),
        }))
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_builtin_domain(&self, domain_kind: BuiltinDomainKind) -> EncodingResult<vir::Domain> {
        if !self.builtin_domains.borrow().contains_key(&domain_kind) {
            let builtin_encoder = BuiltinEncoder::new(self);
            let domain = builtin_encoder.encode_builtin_domain(domain_kind)?;
            self.builtin_domains
                .borrow_mut()
                .insert(domain_kind, domain);
        }
        Ok(self.builtin_domains.borrow()[&domain_kind].clone())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_builtin_domain_type(&self, domain_kind: BuiltinDomainKind) -> EncodingResult<vir::Type> {
        // Also encode the definition, if it's not already under construction.
        let mut domains_in_progress = self.builtin_domains_in_progress.borrow_mut();
        if !domains_in_progress.contains(&domain_kind) {
            domains_in_progress.insert(domain_kind);
            drop(domains_in_progress);
            self.encode_builtin_domain(domain_kind)?;
            domains_in_progress = self.builtin_domains_in_progress.borrow_mut();
            domains_in_progress.remove(&domain_kind);
        }
        let builtin_encoder = BuiltinEncoder::new(self);
        builtin_encoder.encode_builtin_domain_type(domain_kind)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_builtin_method_def(&self, method_kind: BuiltinMethodKind) -> EncodingResult<vir::BodylessMethod> {
        if !self.builtin_methods.borrow().contains_key(&method_kind) {
            let builtin_encoder = BuiltinEncoder::new(self);
            let method = builtin_encoder.encode_builtin_method_def(method_kind)?;
            self.log_vir_program_before_viper(method.to_string());
            self.builtin_methods
                .borrow_mut()
                .insert(method_kind, method);
        }
        Ok(self.builtin_methods.borrow()[&method_kind].clone())
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_builtin_method_use(&self, method_kind: BuiltinMethodKind) -> EncodingResult<String> {
        // Trigger encoding of definition
        self.encode_builtin_method_def(method_kind)?;
        let builtin_encoder = BuiltinEncoder::new(self);
        Ok(builtin_encoder.encode_builtin_method_name(method_kind))
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_cast_function_use(&self, src_ty: ty::Ty<'tcx>, dst_ty: ty::Ty<'tcx>)
        -> EncodingResult<String>
    {
        let function_name = format!("builtin$cast${src_ty}${dst_ty}");
        if !self.type_cast_functions.borrow().contains_key(&(src_ty, dst_ty)) {
            let arg = vir_local!{ number: {self.encode_snapshot_type(src_ty)?} };
            let result = vir_local!{ __result: {self.encode_snapshot_type(dst_ty)?} };
            let mut precondition = self.encode_type_bounds(&arg.clone().into(), src_ty);
            precondition.extend(self.encode_type_bounds(&arg.clone().into(), dst_ty));
            let postcondition = self.encode_type_bounds(&result.into(), dst_ty);
            let function = vir::Function {
                name: function_name.clone(),
                type_arguments: Vec::new(),
                formal_args: vec![arg.clone()],
                return_type: self.encode_snapshot_type(dst_ty)?,
                pres: precondition,
                posts: postcondition,
                body: Some(arg.into()),
            };
            let identifier = self.insert_function(function);
            self.type_cast_functions.borrow_mut().insert((src_ty, dst_ty), identifier);
        }
        Ok(function_name)
    }

    #[tracing::instrument(level = "trace", skip(self))]
    pub fn encode_unsize_function_use(&self, src_ty: ty::Ty<'tcx>, dst_ty: ty::Ty<'tcx>)
        -> EncodingResult<String>
    {
        // at some point we may want to add support for other types of unsizing calls?
        assert!(matches!(src_ty.kind(), ty::TyKind::Array(..) | ty::TyKind::Slice(..)));
        assert!(matches!(dst_ty.kind(), ty::TyKind::Array(..) | ty::TyKind::Slice(..)));

        let array_types = self.encode_sequence_types(src_ty)?;
        let slice_types = self.encode_sequence_types(dst_ty)?;
        let function_name = format!(
            "builtin$unsize${}${}",
            &array_types.sequence_pred_type.name(),
            &slice_types.sequence_pred_type.name()
        );

        if !self.type_cast_functions.borrow().contains_key(&(src_ty, dst_ty)) {
            let src_snap_ty = self.encode_snapshot_type(src_ty)?;
            let dst_snap_ty = self.encode_snapshot_type(dst_ty)?;
            let arg = vir_local!{ array: {src_snap_ty} };
            let arg_expr = vir::Expr::from(arg.clone());
            let array_uncons = self.encode_snapshot_destructor(src_ty, vec![arg_expr.clone()])?;
            let slice_cons = self.encode_snapshot(dst_ty, None, vec![array_uncons.clone()])?;
            let data_len = vir::Expr::ContainerOp(vir::ContainerOp {
                op_kind: vir::ContainerOpKind::SeqLen,
                left: Box::new(array_uncons),
                right: Box::new(true.into()), // unused
                position: vir::Position::default(),
            });
            let result = vir::Expr::from(vir_local!{ __result: {dst_snap_ty.clone()} });
            let postcondition = vec![
                vir_expr!{ [data_len] ==  [array_types.len(self, arg_expr)] },
                vir_expr!{ [result] == [slice_cons]},
            ];
            let function = vir::Function {
                name: function_name.clone(),
                type_arguments: vec![], // FIXME: This is probably wrong.
                formal_args: vec![arg],
                return_type: dst_snap_ty,
                pres: vec![],
                posts: postcondition,
                body: None,
            };
            let identifier = self.insert_function(function);
            self.type_cast_functions.borrow_mut().insert((src_ty, dst_ty), identifier);
        }
        Ok(function_name)
    }

    /// This encodes the Rust function as a Viper method for verification. It
    /// does this also for pure functions.
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn encode_procedure(&self, def_id: ProcedureDefId) -> SpannedEncodingResult<()> {
        assert!(
            !self.is_trusted(def_id, None),
            "procedure is marked as trusted: {def_id:?}"
        );
        if !self.procedures.borrow().contains_key(&def_id) {
            let procedure = self.env.get_procedure(def_id);
            let proc_encoder = ProcedureEncoder::new(self, &procedure)?;
            let mut method = match proc_encoder.encode() {
                Ok(result) => result,
                Err(error) => {
                    self.register_encoding_error(error);
                    StubProcedureEncoder::new(self, &procedure).encode()
                },
            };
            self.log_vir_program_before_viper(method.to_string());

            if config::enable_purification_optimization() {
                purifier::purify_method(self, &mut method);
            }

            self.procedures.borrow_mut().insert(def_id, method);
        }

        Ok(())
    }

    /// Checks whether the given type implements structural equality
    /// by either being a primitive type or by deriving the Eq trait.
    pub fn has_structural_eq_impl(&self, ty: ty::Ty<'tcx>) -> bool {
        let ty = ty.peel_refs();
        let ty = self.env.tcx().erase_regions_ty(ty);
        match ty.kind() {
            ty::TyKind::Bool
            | ty::TyKind::Int(_)
            | ty::TyKind::Uint(_)
            | ty::TyKind::Float(_)
            | ty::TyKind::Char
            | ty::TyKind::Tuple(_)
            | ty::TyKind::Never
            | ty::TyKind::Array(..)
            | ty::TyKind::Slice(..)
            | ty::TyKind::Param(_) => true, // TODO(tymap): this is weird, use substs properly?
            ty::TyKind::Adt(_, _)
            | ty::TyKind::Closure(_, _) => {
                self.env.tcx().has_structural_eq_impls(ty)
            }
            _ => false,
        }
    }

    #[tracing::instrument(level = "debug", skip(self), ret)]
    pub fn encode_const_expr(
        &self,
        ty: ty::Ty<'tcx>,
        value: mir::ConstantKind<'tcx>
    ) -> EncodingResult<vir::Expr> {
        let scalar_value = self.const_eval_intlike(value)?;

        let expr = match ty.kind() {
            ty::TyKind::Bool => scalar_value.to_bool().unwrap().into(),
            ty::TyKind::Char => scalar_value.to_char().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I8) => scalar_value.to_i8().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I16) => scalar_value.to_i16().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I32) => scalar_value.to_i32().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I64) => scalar_value.to_i64().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::I128) => scalar_value.to_i128().unwrap().into(),
            ty::TyKind::Int(ty::IntTy::Isize) => scalar_value.to_target_isize(&self.env.tcx()).unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U8) => scalar_value.to_u8().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U16) => scalar_value.to_u16().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U32) => scalar_value.to_u32().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U64) => scalar_value.to_u64().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::U128) => scalar_value.to_u128().unwrap().into(),
            ty::TyKind::Uint(ty::UintTy::Usize) => scalar_value.to_target_usize(&self.env.tcx()).unwrap().into(),
            ty::TyKind::Float(ty::FloatTy::F32) => {
                let bits = scalar_value.to_u32().unwrap();
                vir::Expr::Const(vir::ConstExpr {
                    value: vir::Const::Float(vir::FloatConst::F32(bits)),
                    position: vir::Position::default(),
                })
            },
            ty::TyKind::Float(ty::FloatTy::F64) => {
                let bits = scalar_value.to_u64().unwrap();
                vir::Expr::Const(vir::ConstExpr {
                    value: vir::Const::Float(vir::FloatConst::F64(bits)),
                    position: vir::Position::default(),
                })
            }
            ty::TyKind::FnDef(..) => {
                vir::Expr::Const(vir::ConstExpr {
                    value: vir::Const::FnPtr,
                    position: vir::Position::default(),
                })
            }
            _ => {
                error_unsupported!("unsupported constant type {:?}", ty.kind());
            }
        };
        Ok(expr)
    }

    #[tracing::instrument(level = "debug", skip(self), ret)]
    pub fn encode_int_cast(&self, value: u128, ty: ty::Ty<'tcx>) -> vir::Expr {
        let expr = match ty.kind() {
            ty::TyKind::Bool => (value != 0).into(),
            ty::TyKind::Int(ty::IntTy::I8) => (value as i8).into(),
            ty::TyKind::Int(ty::IntTy::I16) => (value as i16).into(),
            ty::TyKind::Int(ty::IntTy::I32) => (value as i32).into(),
            ty::TyKind::Int(ty::IntTy::I64) => (value as i64).into(),
            ty::TyKind::Int(ty::IntTy::I128) => (value as i128).into(),
            ty::TyKind::Int(ty::IntTy::Isize) => (value as isize).into(),
            ty::TyKind::Uint(ty::UintTy::U8) => (value as u8).into(),
            ty::TyKind::Uint(ty::UintTy::U16) => (value as u16).into(),
            ty::TyKind::Uint(ty::UintTy::U32) => (value as u32).into(),
            ty::TyKind::Uint(ty::UintTy::U64) => (value as u64).into(),
            ty::TyKind::Uint(ty::UintTy::U128) => value.into(),
            ty::TyKind::Uint(ty::UintTy::Usize) => (value as usize).into(),
            ty::TyKind::Char => value.into(),
            ref x => unimplemented!("{:?}", x),
        };
        expr
    }

    pub fn encode_item_name(&self, def_id: DefId) -> String {
        let full_name = format!("m_{}", encode_identifier(self.env.name.get_unique_item_name(def_id)));
        let short_name = format!("m_{}", encode_identifier(
            self.env.name.get_item_name(def_id)
        ));
        self.intern_viper_identifier(full_name, short_name)
    }

    pub fn queue_procedure_encoding(&self, def_id: ProcedureDefId) {
        self.encoding_queue
            .borrow_mut()
            .push(EncodingTask::Procedure { def_id, substs: Vec::new() });
    }

    pub fn queue_type_encoding(&self, ty: ty::Ty<'tcx>) {
        let mut queued_types = self.queued_types.borrow_mut();
        if !queued_types.contains(&ty) {
            self.encoding_queue
                .borrow_mut()
                .push(EncodingTask::Type { ty });
            queued_types.insert(ty);
        }
    }

    /// Returns true iff `def_id` is a function that uses raw pointers.
    fn is_internally_unsafe_function(&self, def_id: ProcedureDefId) -> bool {
        let mir = self.env.body.borrow_impure_fn_body_identity(def_id.expect_local());
        for local_decl in &mir.local_decls {
            if let prusti_rustc_interface::middle::ty::TyKind::RawPtr(_) =
                local_decl.ty.kind()
            {
                return true;
            }
        }
        false
    }
    #[tracing::instrument(level = "debug", skip(self))]
    pub fn process_encoding_queue(&mut self) {
        if let Err(error) = self.initialize() {
            panic!("The initialization of the encoder failed with the error: {error:?}");
        }
        while let Some(task) = {
            let mut queue = self.encoding_queue.borrow_mut();
            queue.pop()
        } {
            match task {
                EncodingTask::Procedure { def_id: proc_def_id, substs } => {
                    let proc_name = self.env.name.get_unique_item_name(proc_def_id);
                    let proc_def_path = self.env.name.get_item_def_path(proc_def_id);
                    info!("Encoding: {} ({})", proc_name, proc_def_path);
                    assert!(substs.is_empty());

                    if config::unsafe_core_proof() {
                        if self.env.query.is_unsafe_function(proc_def_id) {
                            if let Err(error) = self.encode_lifetimes_core_proof(proc_def_id, CheckMode::UnsafeSafety) {
                                self.register_encoding_error(error);
                                debug!("Error encoding function: {:?} {}", proc_def_id, CheckMode::UnsafeSafety);
                            }
                        } else if config::verify_specifications_with_core_proof() || self.is_internally_unsafe_function(proc_def_id) {
                            if config::verify_core_proof() {
                                if let Err(error) = self.encode_lifetimes_core_proof(proc_def_id, CheckMode::MemorySafety) {
                                    self.register_encoding_error(error);
                                    debug!("Error encoding function: {:?} {}", proc_def_id, CheckMode::MemorySafety);
                                }
                            }
                            if config::verify_specifications() {
                                if let Err(error) = self.encode_lifetimes_core_proof(proc_def_id, CheckMode::MemorySafetyWithFunctional) {
                                    self.register_encoding_error(error);
                                    debug!("Error encoding function: {:?} {}", proc_def_id, CheckMode::MemorySafetyWithFunctional);
                                }
                            }
                        } else {
                            if config::verify_core_proof() {
                                if let Err(error) = self.encode_lifetimes_core_proof(proc_def_id, CheckMode::PurificationSoudness) {
                                    self.register_encoding_error(error);
                                    debug!("Error encoding function: {:?} {}", proc_def_id, CheckMode::PurificationSoudness);
                                }
                            }
                            if config::verify_specifications() {
                                if let Err(error) = self.encode_lifetimes_core_proof(proc_def_id, CheckMode::PurificationFunctional) {
                                    self.register_encoding_error(error);
                                    debug!("Error encoding function: {:?} {}", proc_def_id, CheckMode::PurificationFunctional);
                                }
                            }
                        }
                        continue;
                    }

                    let proc_kind = self.get_proc_kind(proc_def_id, None);

                    if matches!(proc_kind, ProcedureSpecificationKind::Pure) {
                        // Check that the pure Rust function satisfies the basic
                        // requirements by trying to encode it as a Viper function,
                        // which will automatically run the validity checks.

                        // TODO: Make sure that this encoded function does not end up in
                        // the Viper file because that would be unsound.
                        let identity_substs = self.env.query.identity_substs(proc_def_id);
                        if let Err(error) = self.encode_pure_function_def(proc_def_id, proc_def_id, identity_substs) {
                            self.register_encoding_error(error);
                            debug!("Error encoding function: {:?}", proc_def_id);
                            // Skip encoding the function as a method.
                            continue;
                        }
                    }

                    match proc_kind {
                        _ if self.is_trusted(proc_def_id, None) => {
                            debug!(
                                "Trusted procedure will not be encoded or verified: {:?}",
                                proc_def_id
                            );
                        },
                        ProcedureSpecificationKind::Predicate(_) => {
                            debug!(
                                "Predicates will not be encoded or verified: {:?}",
                                proc_def_id
                            );
                        },
                        ProcedureSpecificationKind::Pure |
                        ProcedureSpecificationKind::Impure => {
                            if let Err(error) = self.encode_procedure(proc_def_id) {
                                self.register_encoding_error(error);
                                debug!("Error encoding function: {:?}", proc_def_id);
                            } else {
                                match self.finalize_viper_program(proc_name, proc_def_id) {
                                    Ok(program) => self.programs.push(program),
                                    Err(error) => {
                                        self.register_encoding_error(error);
                                        debug!("Error finalizing program: {:?}", proc_def_id);
                                    }
                                }
                            }
                        }
                    }

                }
                EncodingTask::Type { ty } => {
                    if config::unsafe_core_proof() && config::verify_core_proof() && config::verify_types() {
                        if let Err(error) = self.encode_core_proof_for_type(ty, CheckMode::MemorySafety) {
                            self.register_encoding_error(error);
                            debug!("Error encoding type: {:?} {}", ty, CheckMode::MemorySafety);
                        }
                    }
                }
            }
        }
    }

    pub fn intern_viper_identifier<S: AsRef<str> + Debug>(&self, full_name: S, short_name: S) -> String {
        let result = if config::disable_name_mangling() {
            short_name.as_ref().to_string()
        } else if config::intern_names() {
            self.name_interner.borrow_mut().intern(full_name, &[short_name])
        } else {
            full_name.as_ref().to_string()
        };
        result
    }

    pub fn encode_struct_field_value(
        &self,
        strct: vir::Expr,
        field_name: &str,
        ty: ty::Ty<'tcx>,
    ) -> EncodingResult<vir::Expr> {
        let field = strct.field(self.encode_struct_field(field_name, ty)?);
        self.encode_value_expr(field, ty)
    }
}
