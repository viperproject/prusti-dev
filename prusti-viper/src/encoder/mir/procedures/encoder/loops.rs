use crate::encoder::{
    errors::{ErrorCtxt, SpannedEncodingResult},
    mir::{
        errors::ErrorInterface, places::PlacesEncoderInterface,
        pure::SpecificationEncoderInterface, spans::SpanInterface,
        specifications::SpecificationsInterface, type_layouts::MirTypeLayoutsEncoderInterface,
    },
};
use prusti_rustc_interface::middle::mir;
use vir_crate::high::{self as vir_high};

impl<'p, 'v: 'p, 'tcx: 'v> super::ProcedureEncoder<'p, 'v, 'tcx> {
    pub(super) fn encode_loop_invariant(
        &mut self,
        loop_head: mir::BasicBlock,
        invariant_block: mir::BasicBlock,
        specification_blocks: Vec<mir::BasicBlock>,
    ) -> SpannedEncodingResult<vir_high::Statement> {
        let invariant_location = mir::Location {
            block: invariant_block,
            statement_index: self.mir[invariant_block].statements.len(),
        };
        // Encode functional specification.
        let mut encoded_specs = Vec::new();
        for block in specification_blocks {
            for statement in &self.mir[block].statements {
                if let mir::StatementKind::Assign(box (
                    _,
                    mir::Rvalue::Aggregate(
                        box mir::AggregateKind::Closure(cl_def_id, cl_substs),
                        _,
                    ),
                )) = statement.kind
                {
                    let specification = self.encoder.get_loop_specs(cl_def_id).unwrap();
                    let span = self
                        .encoder
                        .get_definition_span(specification.invariant.to_def_id());
                    let encoded_specification = self.encoder.set_expression_error_ctxt(
                        self.encoder.encode_invariant_high(
                            self.mir,
                            block,
                            self.def_id,
                            cl_substs,
                        )?,
                        span,
                        ErrorCtxt::LoopInvariant,
                        self.def_id,
                    );
                    encoded_specs.push(encoded_specification);
                }
            }
        }
        let encoded_back_edges = {
            let predecessors = self.mir.basic_blocks.predecessors();
            let dominators = self.mir.basic_blocks.dominators();
            predecessors[loop_head]
                .iter()
                .filter(|predecessor| dominators.is_dominated_by(**predecessor, loop_head))
                .map(|back_edge| self.encode_basic_block_label(*back_edge))
                .collect()
        };
        self.init_data.seek_before(invariant_location);

        // Encode permissions.
        let initialized_places = self.initialization.get_after_statement(invariant_location);
        let allocated_locals = self.allocation.get_after_statement(invariant_location);
        let (written_places, mutably_borrowed_places, _) = self
            .procedure
            .loop_info()
            .compute_read_and_write_leaves(loop_head, self.mir, None);

        let mut maybe_modified_places = Vec::new();
        for place in written_places.into_iter().chain(mutably_borrowed_places) {
            if initialized_places.contains_prefix_of(place) {
                maybe_modified_places.push(vir_high::Predicate::owned_non_aliased_no_pos(
                    self.encoder.encode_place_high(self.mir, place, None)?,
                ));
            } else if allocated_locals.contains_prefix_of(place) {
                let mir_type = place.ty(self.mir, self.encoder.env().tcx()).ty;
                let size = self.encoder.encode_type_size_expression(mir_type)?;
                maybe_modified_places.push(vir_high::Predicate::memory_block_stack_no_pos(
                    self.encoder.encode_place_high(self.mir, place, None)?,
                    size,
                ));
            }
        }

        // Encode Lifetime Relations
        let derived_lifetimes = self
            .lifetimes
            .get_origin_contains_loan_at_mid(invariant_location);
        for (derived_lifetime, derived_from) in derived_lifetimes {
            let derived_from_args: Vec<vir_high::Expression> = derived_from
                .iter()
                .map(|x| {
                    vir_high::VariableDecl {
                        name: x.clone(),
                        ty: vir_high::Type::Lifetime,
                    }
                    .into()
                })
                .collect();
            let intersect_expr = vir_high::Expression::builtin_func_app_no_pos(
                vir_high::BuiltinFunc::LifetimeIntersect,
                vec![], // NOTE: we ignore argument_types for LifetimeItersect
                derived_from_args,
                vir_high::ty::Type::Lifetime,
            );
            let equality_expr = vir_high::Expression::binary_op_no_pos(
                vir_high::BinaryOpKind::EqCmp,
                vir_high::VariableDecl {
                    name: derived_lifetime,
                    ty: vir_high::ty::Type::Lifetime,
                }
                .into(),
                intersect_expr,
            );
            encoded_specs.push(equality_expr);
        }

        // Construct the info.
        let loop_invariant = vir_high::Statement::loop_invariant_no_pos(
            self.encode_basic_block_label(loop_head),
            encoded_back_edges,
            maybe_modified_places,
            encoded_specs,
        );
        let statement = self.set_statement_error(
            invariant_location,
            ErrorCtxt::UnexpectedStorageLive,
            loop_invariant,
        )?;
        Ok(statement)
    }
}
