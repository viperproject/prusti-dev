use std::{collections::HashMap, fmt};

use super::super::{legacy, polymorphic};
use uuid::Uuid;

// bodyless_method
impl From<polymorphic::BodylessMethod> for legacy::BodylessMethod {
    fn from(bodyless_method: polymorphic::BodylessMethod) -> legacy::BodylessMethod {
        legacy::BodylessMethod {
            name: bodyless_method.name,
            formal_args: bodyless_method
                .formal_args
                .into_iter()
                .map(|formal_arg| formal_arg.into())
                .collect(),
            formal_returns: bodyless_method
                .formal_returns
                .into_iter()
                .map(|formal_return| formal_return.into())
                .collect(),
        }
    }
}

// common
impl From<polymorphic::PermAmountError> for legacy::PermAmountError {
    fn from(perm_amount_error: polymorphic::PermAmountError) -> legacy::PermAmountError {
        match perm_amount_error {
            polymorphic::PermAmountError::InvalidAdd(perm_amount_1, perm_amount_2) => {
                legacy::PermAmountError::InvalidAdd(perm_amount_1.into(), perm_amount_2.into())
            }
            polymorphic::PermAmountError::InvalidSub(perm_amount_1, perm_amount_2) => {
                legacy::PermAmountError::InvalidSub(perm_amount_1.into(), perm_amount_2.into())
            }
        }
    }
}

impl From<polymorphic::PermAmount> for legacy::PermAmount {
    fn from(perm_amount: polymorphic::PermAmount) -> legacy::PermAmount {
        match perm_amount {
            polymorphic::PermAmount::Read => legacy::PermAmount::Read,
            polymorphic::PermAmount::Write => legacy::PermAmount::Write,
            polymorphic::PermAmount::Remaining => legacy::PermAmount::Remaining,
        }
    }
}

impl From<polymorphic::Type> for legacy::Type {
    fn from(typ: polymorphic::Type) -> legacy::Type {
        match typ {
            polymorphic::Type::Int => legacy::Type::Int,
            polymorphic::Type::Bool => legacy::Type::Bool,
            polymorphic::Type::Seq(seq) => legacy::Type::Seq(Box::new((*seq.typ).into())),
            polymorphic::Type::TypedRef(_) | polymorphic::Type::TypeVar(_) => {
                legacy::Type::TypedRef(typ.encode_as_string())
            }
            polymorphic::Type::Domain(_) => legacy::Type::Domain(typ.encode_as_string()),
            polymorphic::Type::Snapshot(_) => legacy::Type::Snapshot(typ.encode_as_string()),
        }
    }
}

impl From<polymorphic::TypeId> for legacy::TypeId {
    fn from(type_id: polymorphic::TypeId) -> legacy::TypeId {
        match type_id {
            polymorphic::TypeId::Int => legacy::TypeId::Int,
            polymorphic::TypeId::Bool => legacy::TypeId::Bool,
            polymorphic::TypeId::Ref => legacy::TypeId::Ref,
            polymorphic::TypeId::Seq => legacy::TypeId::Seq,
            polymorphic::TypeId::Domain => legacy::TypeId::Domain,
            polymorphic::TypeId::Snapshot => legacy::TypeId::Snapshot,
        }
    }
}

impl From<polymorphic::LocalVar> for legacy::LocalVar {
    fn from(type_id: polymorphic::LocalVar) -> legacy::LocalVar {
        legacy::LocalVar {
            name: type_id.name,
            typ: type_id.typ.into(),
        }
    }
}

impl From<polymorphic::Field> for legacy::Field {
    fn from(field: polymorphic::Field) -> legacy::Field {
        legacy::Field {
            name: field.name,
            typ: field.typ.into(),
        }
    }
}

// domain
impl From<polymorphic::Domain> for legacy::Domain {
    fn from(domain: polymorphic::Domain) -> legacy::Domain {
        legacy::Domain {
            name: domain.name,
            functions: domain
                .functions
                .into_iter()
                .map(|function| function.into())
                .collect(),
            axioms: domain
                .axioms
                .into_iter()
                .map(|axiom| axiom.into())
                .collect(),
            type_vars: domain
                .type_vars
                .into_iter()
                .map(|type_var| type_var.into())
                .collect(),
        }
    }
}

impl From<polymorphic::DomainFunc> for legacy::DomainFunc {
    fn from(domain_func: polymorphic::DomainFunc) -> legacy::DomainFunc {
        legacy::DomainFunc {
            name: domain_func.name,
            formal_args: domain_func
                .formal_args
                .into_iter()
                .map(|formal_arg| formal_arg.into())
                .collect(),
            return_type: domain_func.return_type.into(),
            unique: domain_func.unique,
            domain_name: domain_func.domain_name,
        }
    }
}

impl From<polymorphic::DomainAxiom> for legacy::DomainAxiom {
    fn from(domain_axiom: polymorphic::DomainAxiom) -> legacy::DomainAxiom {
        legacy::DomainAxiom {
            name: domain_axiom.name,
            expr: domain_axiom.expr.into(),
            domain_name: domain_axiom.domain_name,
        }
    }
}

// expr
impl From<polymorphic::Expr> for legacy::Expr {
    fn from(expr: polymorphic::Expr) -> legacy::Expr {
        match expr {
            polymorphic::Expr::Local(local) => {
                legacy::Expr::Local(local.variable.into(), local.position.into())
            }
            polymorphic::Expr::Variant(variant) => legacy::Expr::Variant(
                Box::new((*variant.base).into()),
                variant.variant_index.into(),
                variant.position.into(),
            ),
            polymorphic::Expr::Field(field) => legacy::Expr::Field(
                Box::new((*field.base).into()),
                field.field.into(),
                field.position.into(),
            ),
            polymorphic::Expr::AddrOf(addr_of) => legacy::Expr::AddrOf(
                Box::new((*addr_of.base).into()),
                addr_of.addr_type.into(),
                addr_of.position.into(),
            ),
            polymorphic::Expr::LabelledOld(labelled_old) => legacy::Expr::LabelledOld(
                labelled_old.label,
                Box::new((*labelled_old.base).into()),
                labelled_old.position.into(),
            ),
            polymorphic::Expr::Const(const_expr) => {
                legacy::Expr::Const(const_expr.value.into(), const_expr.position.into())
            }
            polymorphic::Expr::MagicWand(magic_wand) => legacy::Expr::MagicWand(
                Box::new((*magic_wand.left).into()),
                Box::new((*magic_wand.right).into()),
                magic_wand.borrow.map(|borrow| borrow.into()),
                magic_wand.position.into(),
            ),
            polymorphic::Expr::PredicateAccessPredicate(predicate_access_predicate) => {
                legacy::Expr::PredicateAccessPredicate(
                    predicate_access_predicate.predicate_type.encode_as_string(),
                    Box::new((*predicate_access_predicate.argument).into()),
                    predicate_access_predicate.permission.into(),
                    predicate_access_predicate.position.into(),
                )
            }
            polymorphic::Expr::FieldAccessPredicate(field_access_predicate) => {
                legacy::Expr::FieldAccessPredicate(
                    Box::new((*field_access_predicate.base).into()),
                    field_access_predicate.permission.into(),
                    field_access_predicate.position.into(),
                )
            }
            polymorphic::Expr::UnaryOp(unary_op) => legacy::Expr::UnaryOp(
                unary_op.op_kind.into(),
                Box::new((*unary_op.argument).into()),
                unary_op.position.into(),
            ),
            polymorphic::Expr::BinOp(bin_op) => legacy::Expr::BinOp(
                bin_op.op_kind.into(),
                Box::new((*bin_op.left).into()),
                Box::new((*bin_op.right).into()),
                bin_op.position.into(),
            ),
            polymorphic::Expr::ContainerOp(container_op) => legacy::Expr::ContainerOp(
                container_op.op_kind.into(),
                Box::new((*container_op.left).into()),
                Box::new((*container_op.right).into()),
                container_op.position.into(),
            ),
            polymorphic::Expr::Seq(seq) => legacy::Expr::Seq(
                seq.typ.into(),
                seq.elements
                    .into_iter()
                    .map(|element| element.into())
                    .collect(),
                seq.position.into(),
            ),
            polymorphic::Expr::Unfolding(unfolding) => legacy::Expr::Unfolding(
                unfolding.predicate.name(),
                unfolding
                    .arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                Box::new((*unfolding.base).into()),
                unfolding.permission.into(),
                unfolding
                    .variant
                    .map(|enum_variant_index| enum_variant_index.into()),
                unfolding.position.into(),
            ),
            polymorphic::Expr::Cond(cond) => legacy::Expr::Cond(
                Box::new((*cond.guard).into()),
                Box::new((*cond.then_expr).into()),
                Box::new((*cond.else_expr).into()),
                cond.position.into(),
            ),
            polymorphic::Expr::ForAll(for_all) => legacy::Expr::ForAll(
                for_all
                    .variables
                    .into_iter()
                    .map(|variable| variable.into())
                    .collect(),
                for_all
                    .triggers
                    .into_iter()
                    .map(|trigger| trigger.into())
                    .collect(),
                Box::new((*for_all.body).into()),
                for_all.position.into(),
            ),
            polymorphic::Expr::Exists(exists) => legacy::Expr::Exists(
                exists
                    .variables
                    .into_iter()
                    .map(|variable| variable.into())
                    .collect(),
                exists
                    .triggers
                    .into_iter()
                    .map(|trigger| trigger.into())
                    .collect(),
                Box::new((*exists.body).into()),
                exists.position.into(),
            ),
            polymorphic::Expr::LetExpr(let_expr) => legacy::Expr::LetExpr(
                let_expr.variable.into(),
                Box::new((*let_expr.def).into()),
                Box::new((*let_expr.body).into()),
                let_expr.position.into(),
            ),
            polymorphic::Expr::FuncApp(func_app) => legacy::Expr::FuncApp(
                func_app.function_name,
                func_app
                    .arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                func_app
                    .formal_arguments
                    .into_iter()
                    .map(|formal_argument| formal_argument.into())
                    .collect(),
                func_app.return_type.into(),
                func_app.position.into(),
            ),
            polymorphic::Expr::DomainFuncApp(domain_func_app) => legacy::Expr::DomainFuncApp(
                domain_func_app.domain_function.into(),
                domain_func_app
                    .arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                domain_func_app.position.into(),
            ),
            polymorphic::Expr::InhaleExhale(inhale_exhale) => legacy::Expr::InhaleExhale(
                Box::new((*inhale_exhale.inhale_expr).into()),
                Box::new((*inhale_exhale.exhale_expr).into()),
                inhale_exhale.position.into(),
            ),
            polymorphic::Expr::Downcast(down_cast) => legacy::Expr::Downcast(
                Box::new((*down_cast.base).into()),
                Box::new((*down_cast.enum_place).into()),
                down_cast.field.into(),
            ),
            polymorphic::Expr::SnapApp(snap_app) => {
                legacy::Expr::SnapApp(Box::new((*snap_app.base).into()), snap_app.position.into())
            }
        }
    }
}

impl From<polymorphic::PlaceComponent> for legacy::PlaceComponent {
    fn from(place_component: polymorphic::PlaceComponent) -> legacy::PlaceComponent {
        match place_component {
            polymorphic::PlaceComponent::Field(field, position) => {
                legacy::PlaceComponent::Field(field.into(), position.into())
            }
            polymorphic::PlaceComponent::Variant(field, position) => {
                legacy::PlaceComponent::Variant(field.into(), position.into())
            }
        }
    }
}

impl From<polymorphic::UnaryOpKind> for legacy::UnaryOpKind {
    fn from(unary_op_kind: polymorphic::UnaryOpKind) -> legacy::UnaryOpKind {
        match unary_op_kind {
            polymorphic::UnaryOpKind::Not => legacy::UnaryOpKind::Not,
            polymorphic::UnaryOpKind::Minus => legacy::UnaryOpKind::Minus,
        }
    }
}

impl From<polymorphic::BinaryOpKind> for legacy::BinaryOpKind {
    fn from(bin_op_kind: polymorphic::BinaryOpKind) -> legacy::BinaryOpKind {
        match bin_op_kind {
            polymorphic::BinaryOpKind::EqCmp => legacy::BinaryOpKind::EqCmp,
            polymorphic::BinaryOpKind::NeCmp => legacy::BinaryOpKind::NeCmp,
            polymorphic::BinaryOpKind::GtCmp => legacy::BinaryOpKind::GtCmp,
            polymorphic::BinaryOpKind::GeCmp => legacy::BinaryOpKind::GeCmp,
            polymorphic::BinaryOpKind::LtCmp => legacy::BinaryOpKind::LtCmp,
            polymorphic::BinaryOpKind::LeCmp => legacy::BinaryOpKind::LeCmp,
            polymorphic::BinaryOpKind::Add => legacy::BinaryOpKind::Add,
            polymorphic::BinaryOpKind::Sub => legacy::BinaryOpKind::Sub,
            polymorphic::BinaryOpKind::Mul => legacy::BinaryOpKind::Mul,
            polymorphic::BinaryOpKind::Div => legacy::BinaryOpKind::Div,
            polymorphic::BinaryOpKind::Mod => legacy::BinaryOpKind::Mod,
            polymorphic::BinaryOpKind::And => legacy::BinaryOpKind::And,
            polymorphic::BinaryOpKind::Or => legacy::BinaryOpKind::Or,
            polymorphic::BinaryOpKind::Implies => legacy::BinaryOpKind::Implies,
        }
    }
}

impl From<polymorphic::ContainerOpKind> for legacy::ContainerOpKind {
    fn from(container_op_kind: polymorphic::ContainerOpKind) -> legacy::ContainerOpKind {
        match container_op_kind {
            polymorphic::ContainerOpKind::SeqIndex => legacy::ContainerOpKind::SeqIndex,
            polymorphic::ContainerOpKind::SeqConcat => legacy::ContainerOpKind::SeqConcat,
            polymorphic::ContainerOpKind::SeqLen => legacy::ContainerOpKind::SeqLen,
        }
    }
}

impl From<polymorphic::Const> for legacy::Const {
    fn from(old_const: polymorphic::Const) -> legacy::Const {
        match old_const {
            polymorphic::Const::Bool(bool_value) => legacy::Const::Bool(bool_value),
            polymorphic::Const::Int(i64_value) => legacy::Const::Int(i64_value),
            polymorphic::Const::BigInt(label) => legacy::Const::BigInt(label),
            polymorphic::Const::FnPtr => legacy::Const::FnPtr,
        }
    }
}

// function
impl From<polymorphic::Function> for legacy::Function {
    fn from(function: polymorphic::Function) -> legacy::Function {
        legacy::Function {
            name: function.name,
            formal_args: function
                .formal_args
                .into_iter()
                .map(|formal_arg| formal_arg.into())
                .collect(),
            return_type: function.return_type.into(),
            pres: function.pres.into_iter().map(|pre| pre.into()).collect(),
            posts: function.posts.into_iter().map(|post| post.into()).collect(),
            body: function.body.map(|body_expr| body_expr.into()),
        }
    }
}

impl From<polymorphic::FunctionIdentifier> for legacy::FunctionIdentifier {
    fn from(function_identifier: polymorphic::FunctionIdentifier) -> legacy::FunctionIdentifier {
        legacy::FunctionIdentifier(function_identifier.0)
    }
}

// predicate
impl From<polymorphic::Predicate> for legacy::Predicate {
    fn from(predicate: polymorphic::Predicate) -> legacy::Predicate {
        match predicate {
            polymorphic::Predicate::Struct(struct_predicate) => {
                legacy::Predicate::Struct(struct_predicate.into())
            }
            polymorphic::Predicate::Enum(enum_predicate) => {
                legacy::Predicate::Enum(enum_predicate.into())
            }
            polymorphic::Predicate::Bodyless(typ, local_var) => {
                legacy::Predicate::Bodyless(typ.encode_as_string(), local_var.into())
            }
        }
    }
}

impl From<polymorphic::StructPredicate> for legacy::StructPredicate {
    fn from(struct_predicate: polymorphic::StructPredicate) -> legacy::StructPredicate {
        legacy::StructPredicate {
            name: struct_predicate.typ.encode_as_string(),
            this: struct_predicate.this.into(),
            body: struct_predicate.body.map(|body_expr| body_expr.into()),
        }
    }
}

impl From<polymorphic::EnumPredicate> for legacy::EnumPredicate {
    fn from(enum_predicate: polymorphic::EnumPredicate) -> legacy::EnumPredicate {
        legacy::EnumPredicate {
            name: enum_predicate.typ.name(),
            this: enum_predicate.this.into(),
            discriminant_field: enum_predicate.discriminant_field.into(),
            discriminant_bounds: enum_predicate.discriminant_bounds.into(),
            variants: enum_predicate
                .variants
                .into_iter()
                .map(|(expr, label, struct_predicate)| {
                    (expr.into(), label, struct_predicate.into())
                })
                .collect(),
        }
    }
}

impl From<polymorphic::EnumVariantIndex> for legacy::EnumVariantIndex {
    fn from(enum_variant_index: polymorphic::EnumVariantIndex) -> legacy::EnumVariantIndex {
        legacy::EnumVariantIndex::new(enum_variant_index.0)
    }
}

// stmt
impl From<polymorphic::Stmt> for legacy::Stmt {
    fn from(stmt: polymorphic::Stmt) -> legacy::Stmt {
        match stmt {
            polymorphic::Stmt::Comment(comment) => legacy::Stmt::Comment(comment.comment),
            polymorphic::Stmt::Label(label) => legacy::Stmt::Label(label.label),
            polymorphic::Stmt::Inhale(inhale) => legacy::Stmt::Inhale(inhale.expr.into()),
            polymorphic::Stmt::Exhale(exhale) => {
                legacy::Stmt::Exhale(exhale.expr.into(), exhale.position.into())
            }
            polymorphic::Stmt::Assert(assert) => {
                legacy::Stmt::Assert(assert.expr.into(), assert.position.into())
            }
            polymorphic::Stmt::MethodCall(method_call) => legacy::Stmt::MethodCall(
                method_call.method_name,
                method_call
                    .arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                method_call
                    .targets
                    .into_iter()
                    .map(|target| target.into())
                    .collect(),
            ),
            polymorphic::Stmt::Assign(assign) => legacy::Stmt::Assign(
                assign.target.into(),
                assign.source.into(),
                assign.kind.into(),
            ),
            polymorphic::Stmt::Fold(fold) => legacy::Stmt::Fold(
                fold.predicate.name(),
                fold.arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                fold.permission.into(),
                fold.enum_variant
                    .map(|enum_variant_index| enum_variant_index.into()),
                fold.position.into(),
            ),
            polymorphic::Stmt::Unfold(unfold) => legacy::Stmt::Unfold(
                unfold.predicate.name(),
                unfold
                    .arguments
                    .into_iter()
                    .map(|argument| argument.into())
                    .collect(),
                unfold.permission.into(),
                unfold
                    .enum_variant
                    .map(|enum_variant_index| enum_variant_index.into()),
            ),
            polymorphic::Stmt::Obtain(obtain) => {
                legacy::Stmt::Obtain(obtain.expr.into(), obtain.position.into())
            }
            polymorphic::Stmt::BeginFrame(_) => legacy::Stmt::BeginFrame,
            polymorphic::Stmt::EndFrame(_) => legacy::Stmt::EndFrame,
            polymorphic::Stmt::TransferPerm(transfer_perm) => legacy::Stmt::TransferPerm(
                transfer_perm.left.into(),
                transfer_perm.right.into(),
                transfer_perm.unchecked,
            ),
            polymorphic::Stmt::PackageMagicWand(package_magic_wand) => {
                legacy::Stmt::PackageMagicWand(
                    package_magic_wand.magic_wand.into(),
                    package_magic_wand
                        .package_stmts
                        .into_iter()
                        .map(|package_stmt| package_stmt.into())
                        .collect(),
                    package_magic_wand.label,
                    package_magic_wand
                        .variables
                        .into_iter()
                        .map(|variable| variable.into())
                        .collect(),
                    package_magic_wand.position.into(),
                )
            }
            polymorphic::Stmt::ApplyMagicWand(apply_magic_wand) => legacy::Stmt::ApplyMagicWand(
                apply_magic_wand.magic_wand.into(),
                apply_magic_wand.position.into(),
            ),
            polymorphic::Stmt::ExpireBorrows(expire_borrows) => {
                legacy::Stmt::ExpireBorrows(expire_borrows.dag.into())
            }
            polymorphic::Stmt::If(if_stmt) => legacy::Stmt::If(
                if_stmt.guard.into(),
                if_stmt
                    .then_stmts
                    .into_iter()
                    .map(|then_stmt| then_stmt.into())
                    .collect(),
                if_stmt
                    .else_stmts
                    .into_iter()
                    .map(|else_stmt| else_stmt.into())
                    .collect(),
            ),
            polymorphic::Stmt::Downcast(downcast) => {
                legacy::Stmt::Downcast(downcast.base.into(), downcast.field.into())
            }
        }
    }
}

impl From<polymorphic::AssignKind> for legacy::AssignKind {
    fn from(assign_kind: polymorphic::AssignKind) -> legacy::AssignKind {
        match assign_kind {
            polymorphic::AssignKind::Copy => legacy::AssignKind::Copy,
            polymorphic::AssignKind::Move => legacy::AssignKind::Move,
            polymorphic::AssignKind::MutableBorrow(borrow) => {
                legacy::AssignKind::MutableBorrow(borrow.into())
            }
            polymorphic::AssignKind::SharedBorrow(borrow) => {
                legacy::AssignKind::SharedBorrow(borrow.into())
            }
            polymorphic::AssignKind::Ghost => legacy::AssignKind::Ghost,
        }
    }
}

// trigger
impl From<polymorphic::Trigger> for legacy::Trigger {
    fn from(trigger: polymorphic::Trigger) -> legacy::Trigger {
        legacy::Trigger::new(trigger.0.into_iter().map(|expr| expr.into()).collect())
    }
}

// method
impl From<polymorphic::CfgMethod> for legacy::CfgMethod {
    fn from(cfg_method: polymorphic::CfgMethod) -> legacy::CfgMethod {
        legacy::CfgMethod {
            uuid: cfg_method.uuid,
            method_name: cfg_method.method_name,
            formal_arg_count: cfg_method.formal_arg_count,
            formal_returns: cfg_method
                .formal_returns
                .into_iter()
                .map(|formal_return| formal_return.into())
                .collect(),
            local_vars: cfg_method
                .local_vars
                .into_iter()
                .map(|local_var| local_var.into())
                .collect(),
            labels: cfg_method.labels.into_iter().collect(),
            reserved_labels: cfg_method.reserved_labels.into_iter().collect(),
            basic_blocks: cfg_method
                .basic_blocks
                .into_iter()
                .map(|basic_block| basic_block.into())
                .collect(),
            basic_blocks_labels: cfg_method.basic_blocks_labels.into_iter().collect(),
            fresh_var_index: cfg_method.fresh_var_index,
            fresh_label_index: cfg_method.fresh_label_index,
        }
    }
}

impl From<polymorphic::CfgBlock> for legacy::CfgBlock {
    fn from(cfg_block: polymorphic::CfgBlock) -> legacy::CfgBlock {
        legacy::CfgBlock {
            stmts: cfg_block
                .stmts
                .into_iter()
                .map(|stmt| stmt.into())
                .collect(),
            successor: cfg_block.successor.into(),
        }
    }
}

impl From<polymorphic::Successor> for legacy::Successor {
    fn from(successor: polymorphic::Successor) -> legacy::Successor {
        match successor {
            polymorphic::Successor::Undefined => legacy::Successor::Undefined,
            polymorphic::Successor::Return => legacy::Successor::Return,
            polymorphic::Successor::Goto(cfg_block_index) => {
                legacy::Successor::Goto(cfg_block_index.into())
            }
            polymorphic::Successor::GotoSwitch(expr_indices, cfg_block_index) => {
                legacy::Successor::GotoSwitch(
                    expr_indices
                        .into_iter()
                        .map(|(expr, index)| (expr.into(), index.into()))
                        .collect(),
                    cfg_block_index.into(),
                )
            }
        }
    }
}

impl From<polymorphic::CfgBlockIndex> for legacy::CfgBlockIndex {
    fn from(cfg_block_index: polymorphic::CfgBlockIndex) -> legacy::CfgBlockIndex {
        legacy::CfgBlockIndex {
            method_uuid: cfg_block_index.method_uuid,
            block_index: cfg_block_index.block_index,
        }
    }
}

// borrows
impl From<polymorphic::Borrow> for legacy::Borrow {
    fn from(borrow: polymorphic::Borrow) -> legacy::Borrow {
        legacy::Borrow(borrow.0)
    }
}

impl From<polymorphic::Node> for legacy::Node {
    fn from(node: polymorphic::Node) -> legacy::Node {
        legacy::Node {
            guard: node.guard.into(),
            borrow: node.borrow.into(),
            reborrowing_nodes: node
                .reborrowing_nodes
                .into_iter()
                .map(|reborrowing_node| reborrowing_node.into())
                .collect(),
            reborrowed_nodes: node
                .reborrowed_nodes
                .into_iter()
                .map(|reborrowed_node| reborrowed_node.into())
                .collect(),
            stmts: node.stmts.into_iter().map(|stmt| stmt.into()).collect(),
            borrowed_places: node
                .borrowed_places
                .into_iter()
                .map(|borrowed_place| borrowed_place.into())
                .collect(),
            conflicting_borrows: node
                .conflicting_borrows
                .into_iter()
                .map(|conflicting_borrow| conflicting_borrow.into())
                .collect(),
            alive_conflicting_borrows: node
                .alive_conflicting_borrows
                .into_iter()
                .map(|alive_conflicting_borrow| alive_conflicting_borrow.into())
                .collect(),
            place: node.place.map(|expr| expr.into()),
        }
    }
}

impl From<polymorphic::DAG> for legacy::DAG {
    fn from(dag: polymorphic::DAG) -> legacy::DAG {
        legacy::DAG {
            borrow_indices: dag
                .borrow_indices
                .into_iter()
                .map(|(borrow, index)| (borrow.into(), index))
                .collect(),
            nodes: dag.nodes.into_iter().map(|node| node.into()).collect(),
            borrowed_places: dag
                .borrowed_places
                .into_iter()
                .map(|borrowed_place| borrowed_place.into())
                .collect(),
        }
    }
}

// program
impl From<polymorphic::Program> for legacy::Program {
    fn from(program: polymorphic::Program) -> legacy::Program {
        legacy::Program {
            name: program.name,
            domains: program
                .domains
                .into_iter()
                .map(|domain| domain.into())
                .collect(),
            fields: program
                .fields
                .into_iter()
                .map(|field| field.into())
                .collect(),
            builtin_methods: program
                .builtin_methods
                .into_iter()
                .map(|builtin_method| builtin_method.into())
                .collect(),
            methods: program
                .methods
                .into_iter()
                .map(|method| method.into())
                .collect(),
            functions: program
                .functions
                .into_iter()
                .map(|function| function.into())
                .collect(),
            viper_predicates: program
                .viper_predicates
                .into_iter()
                .map(|viper_predicate| viper_predicate.into())
                .collect(),
        }
    }
}
