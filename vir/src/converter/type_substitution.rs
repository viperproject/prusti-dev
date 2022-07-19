use rustc_hash::FxHashMap;
use std::fmt;

use super::super::polymorphic::*;
use uuid::Uuid;

pub trait Generic {
    #[must_use]
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self;
}

// bodyless_method
impl Generic for BodylessMethod {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut bodyless_method = self;
        bodyless_method.formal_args = bodyless_method
            .formal_args
            .into_iter()
            .map(|formal_arg| formal_arg.substitute(map))
            .collect();
        bodyless_method.formal_returns = bodyless_method
            .formal_returns
            .into_iter()
            .map(|formal_return| formal_return.substitute(map))
            .collect();
        bodyless_method
    }
}

// common
impl Generic for Type {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        match self {
            Type::Bool | Type::Int | Type::Float(..) | Type::BitVector(..) => self,
            Type::Seq(mut seq) => {
                let typ = *seq.typ;
                *seq.typ = typ.substitute(map);
                Type::Seq(seq)
            }
            Type::Map(mut m) => {
                *m.key_type = m.key_type.substitute(map);
                *m.val_type = m.val_type.substitute(map);
                Type::Map(m)
            }
            Type::TypedRef(mut typed_ref) => {
                typed_ref.arguments = typed_ref
                    .arguments
                    .into_iter()
                    .map(|arg| arg.substitute(map))
                    .collect();
                Type::TypedRef(typed_ref)
            }
            Type::Domain(mut domain_type) => {
                domain_type.arguments = domain_type
                    .arguments
                    .into_iter()
                    .map(|arg| arg.substitute(map))
                    .collect();
                Type::Domain(domain_type)
            }
            Type::Snapshot(mut snapshot_type) => {
                snapshot_type.arguments = snapshot_type
                    .arguments
                    .into_iter()
                    .map(|arg| arg.substitute(map))
                    .collect();
                Type::Snapshot(snapshot_type)
            }
            Type::TypeVar(type_var) => match map.get(&type_var) {
                Some(substituted_typ) => substituted_typ.clone(),
                _ => Type::TypeVar(type_var),
            },
        }
    }
}

impl Generic for LocalVar {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut local_var = self;
        local_var.typ = local_var.typ.substitute(map);
        local_var
    }
}

impl Generic for Field {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut field = self;
        field.typ = field.typ.substitute(map);
        field
    }
}

// domain
impl Generic for Domain {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut domain = self;
        domain.functions = domain
            .functions
            .into_iter()
            .map(|function| function.substitute(map))
            .collect();
        domain.axioms = domain
            .axioms
            .into_iter()
            .map(|axiom| axiom.substitute(map))
            .collect();
        domain.type_vars = domain
            .type_vars
            .into_iter()
            .map(|type_var| type_var.substitute(map))
            .collect();
        domain
    }
}

impl Generic for DomainFunc {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut domain_func = self;
        domain_func.formal_args = domain_func
            .formal_args
            .into_iter()
            .map(|formal_arg| formal_arg.substitute(map))
            .collect();
        domain_func.return_type = domain_func.return_type.substitute(map);
        domain_func
    }
}

impl Generic for DomainAxiom {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut domain_axiom = self;
        domain_axiom.expr = domain_axiom.expr.substitute(map);
        domain_axiom
    }
}

// expr
impl Generic for Expr {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        match self {
            Expr::Local(local) => Expr::Local(local.substitute(map)),
            Expr::Variant(variant) => Expr::Variant(variant.substitute(map)),
            Expr::Field(field) => Expr::Field(field.substitute(map)),
            Expr::AddrOf(addr_of) => Expr::AddrOf(addr_of.substitute(map)),
            Expr::LabelledOld(labelled_old) => Expr::LabelledOld(labelled_old.substitute(map)),
            Expr::Const(const_expr) => Expr::Const(const_expr.substitute(map)),
            Expr::MagicWand(magic_wand) => Expr::MagicWand(magic_wand.substitute(map)),
            Expr::PredicateAccessPredicate(predicate_access_predicate) => {
                Expr::PredicateAccessPredicate(predicate_access_predicate.substitute(map))
            }
            Expr::FieldAccessPredicate(field_access_predicate) => {
                Expr::FieldAccessPredicate(field_access_predicate.substitute(map))
            }
            Expr::UnaryOp(unary_op) => Expr::UnaryOp(unary_op.substitute(map)),
            Expr::BinOp(bin_op) => Expr::BinOp(bin_op.substitute(map)),
            Expr::ContainerOp(container_op) => Expr::ContainerOp(container_op.substitute(map)),
            Expr::Seq(seq) => Expr::Seq(seq.substitute(map)),
            Expr::Map(emap) => Expr::Map(emap.substitute(map)),
            Expr::Unfolding(unfolding) => Expr::Unfolding(unfolding.substitute(map)),
            Expr::Cond(cond) => Expr::Cond(cond.substitute(map)),
            Expr::ForAll(for_all) => Expr::ForAll(for_all.substitute(map)),
            Expr::Exists(exists) => Expr::Exists(exists.substitute(map)),
            Expr::LetExpr(let_expr) => Expr::LetExpr(let_expr.substitute(map)),
            Expr::FuncApp(func_app) => Expr::FuncApp(func_app.substitute(map)),
            Expr::DomainFuncApp(domain_func_app) => {
                Expr::DomainFuncApp(domain_func_app.substitute(map))
            }
            Expr::InhaleExhale(inhale_exhale) => Expr::InhaleExhale(inhale_exhale.substitute(map)),
            Expr::Downcast(down_cast) => Expr::Downcast(down_cast.substitute(map)),
            Expr::SnapApp(snap_app) => Expr::SnapApp(snap_app.substitute(map)),
            Expr::Cast(cast) => Expr::Cast(cast.substitute(map)),
        }
    }
}

impl Generic for Local {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut local = self;
        local.variable = local.variable.substitute(map);
        local
    }
}

impl Generic for Variant {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut variant = self;
        *variant.base = variant.base.substitute(map);
        variant.variant_index = variant.variant_index.substitute(map);
        variant
    }
}

impl Generic for FieldExpr {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut field_expr = self;
        *field_expr.base = field_expr.base.substitute(map);
        field_expr.field = field_expr.field.substitute(map);
        field_expr
    }
}

impl Generic for AddrOf {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut addr_of = self;
        *addr_of.base = addr_of.base.substitute(map);
        addr_of.addr_type = addr_of.addr_type.substitute(map);
        addr_of
    }
}

impl Generic for LabelledOld {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut labelled_old = self;
        *labelled_old.base = labelled_old.base.substitute(map);
        labelled_old
    }
}

impl Generic for ConstExpr {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for MagicWand {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut magic_wand = self;
        *magic_wand.left = magic_wand.left.substitute(map);
        *magic_wand.right = magic_wand.right.substitute(map);
        magic_wand.borrow = magic_wand.borrow.map(|borrow| borrow.substitute(map));
        magic_wand
    }
}

impl Generic for PredicateAccessPredicate {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut predicate_access_predicate = self;
        *predicate_access_predicate.argument = predicate_access_predicate.argument.substitute(map);
        predicate_access_predicate
    }
}

impl Generic for FieldAccessPredicate {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut field_access_predicate = self;
        *field_access_predicate.base = field_access_predicate.base.substitute(map);
        field_access_predicate
    }
}

impl Generic for UnaryOp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut unary_op = self;
        *unary_op.argument = unary_op.argument.substitute(map);
        unary_op
    }
}

impl Generic for BinOp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut bin_op = self;
        *bin_op.left = bin_op.left.substitute(map);
        *bin_op.right = bin_op.right.substitute(map);
        bin_op
    }
}

impl Generic for ContainerOp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut container_op = self;
        *container_op.left = container_op.left.substitute(map);
        *container_op.right = container_op.right.substitute(map);
        container_op
    }
}

impl Generic for Seq {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut seq = self;
        seq.typ = seq.typ.substitute(map);
        seq.elements = seq
            .elements
            .into_iter()
            .map(|element| element.substitute(map))
            .collect();
        seq
    }
}

impl Generic for Map {
    fn substitute(self, sub: &FxHashMap<TypeVar, Type>) -> Self {
        let mut map = self;
        map.typ = map.typ.substitute(sub);
        map.elements = map
            .elements
            .into_iter()
            .map(|element| element.substitute(sub))
            .collect();
        map
    }
}

impl Generic for Unfolding {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut unfolding = self;
        unfolding.arguments = unfolding
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        *unfolding.base = unfolding.base.substitute(map);
        unfolding.variant = unfolding
            .variant
            .map(|enum_variant_index| enum_variant_index.substitute(map));
        unfolding
    }
}

impl Generic for Cond {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut cond = self;
        *cond.guard = cond.guard.substitute(map);
        *cond.then_expr = cond.then_expr.substitute(map);
        *cond.else_expr = cond.else_expr.substitute(map);
        cond
    }
}

impl Generic for ForAll {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut for_all = self;
        for_all.variables = for_all
            .variables
            .into_iter()
            .map(|variable| variable.substitute(map))
            .collect();
        for_all.triggers = for_all
            .triggers
            .into_iter()
            .map(|trigger| trigger.substitute(map))
            .collect();
        *for_all.body = for_all.body.substitute(map);
        for_all
    }
}

impl Generic for Exists {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut exists = self;
        exists.variables = exists
            .variables
            .into_iter()
            .map(|variable| variable.substitute(map))
            .collect();
        exists.triggers = exists
            .triggers
            .into_iter()
            .map(|trigger| trigger.substitute(map))
            .collect();
        *exists.body = exists.body.substitute(map);
        exists
    }
}

impl Generic for LetExpr {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut let_expr = self;
        let_expr.variable = let_expr.variable.substitute(map);
        *let_expr.def = let_expr.def.substitute(map);
        *let_expr.body = let_expr.body.substitute(map);
        let_expr
    }
}

impl Generic for FuncApp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut func_app = self;
        func_app.arguments = func_app
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        func_app.formal_arguments = func_app
            .formal_arguments
            .into_iter()
            .map(|formal_argument| formal_argument.substitute(map))
            .collect();
        func_app.return_type = func_app.return_type.substitute(map);
        func_app
    }
}

impl Generic for DomainFuncApp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut domain_func_app = self;
        domain_func_app.domain_function = domain_func_app.domain_function.substitute(map);
        domain_func_app.arguments = domain_func_app
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        domain_func_app
    }
}

impl Generic for InhaleExhale {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut inhale_exhale = self;
        *inhale_exhale.inhale_expr = inhale_exhale.inhale_expr.substitute(map);
        *inhale_exhale.exhale_expr = inhale_exhale.exhale_expr.substitute(map);
        inhale_exhale
    }
}

impl Generic for DowncastExpr {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut downcast = self;
        *downcast.base = downcast.base.substitute(map);
        *downcast.enum_place = downcast.enum_place.substitute(map);
        downcast.field = downcast.field.substitute(map);
        downcast
    }
}

impl Generic for SnapApp {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut snap_app = self;
        *snap_app.base = snap_app.base.substitute(map);
        snap_app
    }
}

impl Generic for Cast {
    fn substitute(mut self, map: &FxHashMap<TypeVar, Type>) -> Self {
        *self.base = self.base.substitute(map);
        self
    }
}

// function
impl Generic for Function {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut function = self;
        function.formal_args = function
            .formal_args
            .into_iter()
            .map(|formal_arg| formal_arg.substitute(map))
            .collect();
        function.return_type = function.return_type.substitute(map);
        function.pres = function
            .pres
            .into_iter()
            .map(|pre| pre.substitute(map))
            .collect();
        function.posts = function
            .posts
            .into_iter()
            .map(|post| post.substitute(map))
            .collect();
        function.body = function.body.map(|body_expr| body_expr.substitute(map));
        function
    }
}

// predicate
impl Generic for Predicate {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        match self {
            Predicate::Struct(struct_predicate) => {
                Predicate::Struct(struct_predicate.substitute(map))
            }
            Predicate::Enum(enum_predicate) => Predicate::Enum(enum_predicate.substitute(map)),
            Predicate::Bodyless(label, local_var) => {
                Predicate::Bodyless(label, local_var.substitute(map))
            }
        }
    }
}

impl Generic for StructPredicate {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut struct_predicate = self;
        struct_predicate.this = struct_predicate.this.substitute(map);
        struct_predicate.body = struct_predicate.body.map(|expr| expr.substitute(map));
        struct_predicate
    }
}

impl Generic for EnumPredicate {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut enum_predicate = self;
        enum_predicate.this = enum_predicate.this.substitute(map);
        enum_predicate.discriminant_field = enum_predicate.discriminant_field.substitute(map);
        enum_predicate.discriminant_bounds = enum_predicate.discriminant_bounds.substitute(map);
        enum_predicate.variants = enum_predicate
            .variants
            .into_iter()
            .map(|(expr, label, struct_predicate)| {
                (
                    expr.substitute(map),
                    label,
                    struct_predicate.substitute(map),
                )
            })
            .collect();
        enum_predicate
    }
}

impl Generic for EnumVariantIndex {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

// stmt
impl Generic for Stmt {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        match self {
            Stmt::Comment(comment) => Stmt::Comment(comment.substitute(map)),
            Stmt::Label(label) => Stmt::Label(label.substitute(map)),
            Stmt::Inhale(inhale) => Stmt::Inhale(inhale.substitute(map)),
            Stmt::Exhale(exhale) => Stmt::Exhale(exhale.substitute(map)),
            Stmt::Assert(assert) => Stmt::Assert(assert.substitute(map)),
            Stmt::MethodCall(method_call) => Stmt::MethodCall(method_call.substitute(map)),
            Stmt::Assign(assign) => Stmt::Assign(assign.substitute(map)),
            Stmt::Fold(fold) => Stmt::Fold(fold.substitute(map)),
            Stmt::Unfold(unfold) => Stmt::Unfold(unfold.substitute(map)),
            Stmt::Obtain(obtain) => Stmt::Obtain(obtain.substitute(map)),
            Stmt::BeginFrame(begin_frame) => Stmt::BeginFrame(begin_frame.substitute(map)),
            Stmt::EndFrame(end_frame) => Stmt::EndFrame(end_frame.substitute(map)),
            Stmt::TransferPerm(transfer_perm) => Stmt::TransferPerm(transfer_perm.substitute(map)),
            Stmt::PackageMagicWand(package_magic_wand) => {
                Stmt::PackageMagicWand(package_magic_wand.substitute(map))
            }
            Stmt::ApplyMagicWand(apply_magic_wand) => {
                Stmt::ApplyMagicWand(apply_magic_wand.substitute(map))
            }
            Stmt::ExpireBorrows(expire_borrows) => {
                Stmt::ExpireBorrows(expire_borrows.substitute(map))
            }
            Stmt::If(if_stmt) => Stmt::If(if_stmt.substitute(map)),
            Stmt::Downcast(downcast) => Stmt::Downcast(downcast.substitute(map)),
        }
    }
}

// trigger
impl Generic for Trigger {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut trigger = self;
        trigger.0 = trigger
            .0
            .into_iter()
            .map(|expr| expr.substitute(map))
            .collect();
        trigger
    }
}

impl Generic for Comment {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for Label {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for Inhale {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut inhale = self;
        inhale.expr = inhale.expr.substitute(map);
        inhale
    }
}

impl Generic for Exhale {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut exhale = self;
        exhale.expr = exhale.expr.substitute(map);
        exhale
    }
}

impl Generic for Assert {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut assert = self;
        assert.expr = assert.expr.substitute(map);
        assert
    }
}

impl Generic for MethodCall {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut method_call = self;
        method_call.arguments = method_call
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        method_call.targets = method_call
            .targets
            .into_iter()
            .map(|target| target.substitute(map))
            .collect();
        method_call
    }
}

impl Generic for Assign {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut assign = self;
        assign.target = assign.target.substitute(map);
        assign.source = assign.source.substitute(map);
        assign
    }
}

impl Generic for Fold {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut fold = self;
        fold.arguments = fold
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        fold.enum_variant = fold
            .enum_variant
            .map(|enum_variant_index| enum_variant_index.substitute(map));
        fold
    }
}

impl Generic for Unfold {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut unfold = self;
        unfold.arguments = unfold
            .arguments
            .into_iter()
            .map(|argument| argument.substitute(map))
            .collect();
        unfold.enum_variant = unfold
            .enum_variant
            .map(|enum_variant_index| enum_variant_index.substitute(map));
        unfold
    }
}

impl Generic for Obtain {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut obtain = self;
        obtain.expr = obtain.expr.substitute(map);
        obtain
    }
}

impl Generic for BeginFrame {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for EndFrame {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for TransferPerm {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut transfer_perm = self;
        transfer_perm.left = transfer_perm.left.substitute(map);
        transfer_perm.right = transfer_perm.right.substitute(map);
        transfer_perm
    }
}

impl Generic for PackageMagicWand {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut package_magic_wand = self;
        package_magic_wand.magic_wand = package_magic_wand.magic_wand.substitute(map);
        package_magic_wand.package_stmts = package_magic_wand
            .package_stmts
            .into_iter()
            .map(|package_stmt| package_stmt.substitute(map))
            .collect();
        package_magic_wand.variables = package_magic_wand
            .variables
            .into_iter()
            .map(|variable| variable.substitute(map))
            .collect();
        package_magic_wand
    }
}

impl Generic for ApplyMagicWand {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut apply_magic_wand = self;
        apply_magic_wand.magic_wand = apply_magic_wand.magic_wand.substitute(map);
        apply_magic_wand
    }
}

impl Generic for ExpireBorrows {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut expire_borrows = self;
        expire_borrows.dag = expire_borrows.dag.substitute(map);
        expire_borrows
    }
}

impl Generic for If {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut if_stmt = self;
        if_stmt.guard = if_stmt.guard.substitute(map);
        if_stmt.then_stmts = if_stmt
            .then_stmts
            .into_iter()
            .map(|then_stmt| then_stmt.substitute(map))
            .collect();
        if_stmt.else_stmts = if_stmt
            .else_stmts
            .into_iter()
            .map(|else_stmt| else_stmt.substitute(map))
            .collect();
        if_stmt
    }
}

impl Generic for Downcast {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut downcast = self;
        downcast.base = downcast.base.substitute(map);
        downcast.field = downcast.field.substitute(map);
        downcast
    }
}

// method
impl Generic for CfgMethod {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut cfg_method = self;
        cfg_method.formal_returns = cfg_method
            .formal_returns
            .into_iter()
            .map(|formal_return| formal_return.substitute(map))
            .collect();
        cfg_method.local_vars = cfg_method
            .local_vars
            .into_iter()
            .map(|local_var| local_var.substitute(map))
            .collect();
        cfg_method.basic_blocks = cfg_method
            .basic_blocks
            .into_iter()
            .map(|basic_block| basic_block.substitute(map))
            .collect();
        cfg_method
    }
}

impl Generic for CfgBlock {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut cfg_block = self;
        cfg_block.stmts = cfg_block
            .stmts
            .into_iter()
            .map(|stmt| stmt.substitute(map))
            .collect();
        cfg_block.successor = cfg_block.successor.substitute(map);
        cfg_block
    }
}

impl Generic for Successor {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        match self {
            Successor::Undefined | Successor::Return => self,
            Successor::Goto(cfg_block_index) => Successor::Goto(cfg_block_index.substitute(map)),
            Successor::GotoSwitch(expr_indices, cfg_block_index) => Successor::GotoSwitch(
                expr_indices
                    .into_iter()
                    .map(|(expr, index)| (expr.substitute(map), index.substitute(map)))
                    .collect(),
                cfg_block_index.substitute(map),
            ),
        }
    }
}

impl Generic for CfgBlockIndex {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

// borrows
impl Generic for Borrow {
    fn substitute(self, _map: &FxHashMap<TypeVar, Type>) -> Self {
        self
    }
}

impl Generic for Node {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut node = self;
        node.guard = node.guard.substitute(map);
        node.borrow = node.borrow.substitute(map);
        node.reborrowing_nodes = node
            .reborrowing_nodes
            .into_iter()
            .map(|reborrowing_node| reborrowing_node.substitute(map))
            .collect();
        node.reborrowed_nodes = node
            .reborrowed_nodes
            .into_iter()
            .map(|reborrowed_nodes| reborrowed_nodes.substitute(map))
            .collect();
        node.stmts = node
            .stmts
            .into_iter()
            .map(|stmt| stmt.substitute(map))
            .collect();
        node.borrowed_places = node
            .borrowed_places
            .into_iter()
            .map(|borrowed_place| borrowed_place.substitute(map))
            .collect();
        node.conflicting_borrows = node
            .conflicting_borrows
            .into_iter()
            .map(|conflicting_borrow| conflicting_borrow.substitute(map))
            .collect();
        node.alive_conflicting_borrows = node
            .alive_conflicting_borrows
            .into_iter()
            .map(|alive_conflicting_borrow| alive_conflicting_borrow.substitute(map))
            .collect();
        node.place = node.place.map(|expr| expr.substitute(map));
        node
    }
}

impl Generic for DAG {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut dag = self;
        dag.borrow_indices = dag
            .borrow_indices
            .into_iter()
            .map(|(borrow, index)| (borrow.substitute(map), index))
            .collect();
        dag.nodes = dag
            .nodes
            .into_iter()
            .map(|node| node.substitute(map))
            .collect();
        dag.borrowed_places = dag
            .borrowed_places
            .into_iter()
            .map(|borrowed_place| borrowed_place.substitute(map))
            .collect();
        dag
    }
}

// program
impl Generic for Program {
    fn substitute(self, map: &FxHashMap<TypeVar, Type>) -> Self {
        let mut program = self;
        program.domains = program
            .domains
            .into_iter()
            .map(|domain| domain.substitute(map))
            .collect();
        program.fields = program
            .fields
            .into_iter()
            .map(|field| field.substitute(map))
            .collect();
        program.builtin_methods = program
            .builtin_methods
            .into_iter()
            .map(|builtin_method| builtin_method.substitute(map))
            .collect();
        program.methods = program
            .methods
            .into_iter()
            .map(|method| method.substitute(map))
            .collect();
        program.functions = program
            .functions
            .into_iter()
            .map(|function| function.substitute(map))
            .collect();
        program.viper_predicates = program
            .viper_predicates
            .into_iter()
            .map(|viper_predicate| viper_predicate.substitute(map))
            .collect();
        program
    }
}

// below are tests for various levels in the vir structure
#[cfg(test)]
mod tests {
    use super::*;

    lazy_static::lazy_static! {
        static ref SUBSTITUTION_MAP : FxHashMap<TypeVar, Type> = {
            let mut m = FxHashMap::default();
            m.insert(TypeVar { label: String::from("T") }, Type::Int);
            m.insert(TypeVar { label: String::from("E") }, Type::Bool);
            m.insert(TypeVar { label: String::from("F") }, Type::typed_ref("SimpleRef"));
            // Substitution into other type vars that have a mapping
            m.insert(TypeVar { label: String::from("G") }, Type::typed_ref_with_args("ComplexRef", vec![Type::type_var("T")]));
            // Subsitutition into the same type vars used for substitution
            m.insert(TypeVar { label: String::from("H") }, Type::typed_ref_with_args(
                "ComplexRef2",
                vec![
                    Type::type_var("H"),
                    Type::domain_with_args(
                        "ComplexDomain",
                        vec![Type::type_var("T")],
                    )
                ],
            ));
            m
        };
    }

    // Compare the results after substitution with expected value
    fn test<T>(source: T, expected: T, map: &FxHashMap<TypeVar, Type>)
    where
        T: Generic,
        T: fmt::Debug,
        T: PartialEq,
    {
        let substituted = source.substitute(map);
        assert_eq!(substituted, expected);
    }

    #[test]
    // source having no type var for substitution
    fn substitution_no_type_var_test() {
        let mut source = Type::Int;
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::Bool;
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::typed_ref_with_args("CustomStruct", vec![Type::Int]);
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::domain("CustomDomain");
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::snapshot_with_args(
            "CustomSnapshot",
            vec![
                Type::Bool,
                Type::typed_ref_with_args("vec", vec![Type::Bool]),
            ],
        );
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::type_var("CustomTypeVar");
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // source having no matching type var for substitution
    fn substitution_no_matching_type_var_test() {
        let mut source = Type::typed_ref_with_args("CustomStruct", vec![Type::type_var("D")]);
        let mut expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::domain_with_args(
            "CustomDomain",
            vec![Type::type_var("C"), Type::Int, Type::type_var("D")],
        );
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::snapshot_with_args(
            "Custom",
            vec![
                Type::Bool,
                Type::typed_ref_with_args("vec", vec![Type::type_var("D")]),
            ],
        );
        expected = source.clone();
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution simple case
    fn substitution_type_var_simple_test() {
        let mut source = Type::type_var("T");
        let mut expected = Type::Int;
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::typed_ref_with_args(
            "CustomStruct",
            vec![Type::type_var("E"), Type::type_var("F")],
        );
        expected = Type::typed_ref_with_args(
            "CustomStruct",
            vec![Type::Bool, Type::typed_ref("SimpleRef")],
        );
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::domain_with_args(
            "CustomDomain",
            vec![Type::type_var("E"), Type::type_var("F")],
        );
        expected = Type::domain_with_args(
            "CustomDomain",
            vec![Type::Bool, Type::typed_ref("SimpleRef")],
        );
        test(source, expected, &SUBSTITUTION_MAP);

        source = Type::snapshot_with_args(
            "CustomSnapshot",
            vec![Type::type_var("E"), Type::type_var("F")],
        );
        expected = Type::snapshot_with_args(
            "CustomSnapshot",
            vec![Type::Bool, Type::typed_ref("SimpleRef")],
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution more complex case
    fn substitution_type_var_complex_test() {
        // more nested structure
        let source = Type::typed_ref_with_args(
            "CustomStruct",
            vec![
                Type::Int,
                Type::domain_with_args(
                    "CustomDomain",
                    vec![
                        Type::type_var("E"),
                        Type::snapshot_with_args("CustomSnapshot", vec![Type::type_var("F")]),
                    ],
                ),
            ],
        );
        let expected = Type::typed_ref_with_args(
            "CustomStruct",
            vec![
                Type::Int,
                Type::domain_with_args(
                    "CustomDomain",
                    vec![
                        Type::Bool,
                        Type::snapshot_with_args(
                            "CustomSnapshot",
                            vec![Type::typed_ref("SimpleRef")],
                        ),
                    ],
                ),
            ],
        );
        test(source, expected, &SUBSTITUTION_MAP);

        // structures having type vars after substitution
        let source = Type::typed_ref_with_args(
            "CustomStruct",
            vec![
                Type::type_var("G"),
                Type::domain_with_args(
                    "CustomDomain",
                    vec![
                        Type::type_var("H"),
                        Type::snapshot_with_args("CustomSnapshot", vec![Type::type_var("F")]),
                    ],
                ),
            ],
        );
        let expected = Type::typed_ref_with_args(
            "CustomStruct",
            vec![
                Type::typed_ref_with_args("ComplexRef", vec![Type::type_var("T")]),
                Type::domain_with_args(
                    "CustomDomain",
                    vec![
                        Type::typed_ref_with_args(
                            "ComplexRef2",
                            vec![
                                Type::type_var("H"),
                                Type::domain_with_args("ComplexDomain", vec![Type::type_var("T")]),
                            ],
                        ),
                        Type::snapshot_with_args(
                            "CustomSnapshot",
                            vec![Type::typed_ref("SimpleRef")],
                        ),
                    ],
                ),
            ],
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within LocalVar
    fn substitution_type_var_local_var_test() {
        let source = LocalVar {
            name: String::from("_v1"),
            typ: Type::type_var("T"),
        };
        let expected = LocalVar {
            name: String::from("_v1"),
            typ: Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Field
    fn substitution_type_var_field_test() {
        let source = Field {
            name: String::from("_f1"),
            typ: Type::type_var("T"),
        };
        let expected = Field {
            name: String::from("_f1"),
            typ: Type::Int,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Expr, going over all variants
    fn substitution_type_var_expr_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Local
        let mut source = Expr::Local(Local {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
            position,
        });
        let mut expected = Expr::Local(Local {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Variant
        source = Expr::Variant(Variant {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            variant_index: Field {
                name: String::from("_f1"),
                typ: Type::type_var("T"),
            },
            position,
        });
        expected = Expr::Variant(Variant {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            variant_index: Field {
                name: String::from("_f1"),
                typ: Type::Int,
            },
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Field
        source = Expr::Field(FieldExpr {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            field: Field {
                name: String::from("_f1"),
                typ: Type::type_var("T"),
            },
            position,
        });
        expected = Expr::Field(FieldExpr {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            field: Field {
                name: String::from("_f1"),
                typ: Type::Int,
            },
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // AddrOf
        source = Expr::AddrOf(AddrOf {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            addr_type: Type::type_var("E"),
            position,
        });
        expected = Expr::AddrOf(AddrOf {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            addr_type: Type::Bool,
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LabelledOld
        source = Expr::LabelledOld(LabelledOld {
            label: String::from("l1"),
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::LabelledOld(LabelledOld {
            label: String::from("l1"),
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Const
        source = Expr::Const(ConstExpr {
            value: Const::Int(123),
            position,
        });
        expected = Expr::Const(ConstExpr {
            value: Const::Int(123),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MagicWand
        source = Expr::MagicWand(MagicWand {
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_left"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_right"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            borrow: Some(Borrow(123)),
            position,
        });
        expected = Expr::MagicWand(MagicWand {
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_left"),
                    typ: Type::Int,
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_right"),
                    typ: Type::Bool,
                },
                position,
            })),
            borrow: Some(Borrow(123)),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PredicateAccessPredicate
        source = Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type: Type::typed_ref("_p1"),
            argument: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            permission: PermAmount::Read,
            position,
        });
        expected = Expr::PredicateAccessPredicate(PredicateAccessPredicate {
            predicate_type: Type::typed_ref("_p1"),
            argument: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            permission: PermAmount::Read,
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FieldAccessPredicate
        source = Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            permission: PermAmount::Read,
            position,
        });
        expected = Expr::FieldAccessPredicate(FieldAccessPredicate {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            permission: PermAmount::Read,
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // UnaryOp
        source = Expr::UnaryOp(UnaryOp {
            op_kind: UnaryOpKind::Minus,
            argument: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::UnaryOp(UnaryOp {
            op_kind: UnaryOpKind::Minus,
            argument: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BinOp
        source = Expr::BinOp(BinOp {
            op_kind: BinaryOpKind::Mul,
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            position,
        });
        expected = Expr::BinOp(BinOp {
            op_kind: BinaryOpKind::Mul,
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ContainerOp
        source = Expr::ContainerOp(ContainerOp {
            op_kind: ContainerOpKind::SeqConcat,
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            position,
        });
        expected = Expr::ContainerOp(ContainerOp {
            op_kind: ContainerOpKind::SeqConcat,
            left: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            right: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Seq
        source = Expr::Seq(Seq {
            typ: Type::type_var("T"),
            elements: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ],
            position,
        });
        expected = Expr::Seq(Seq {
            typ: Type::Int,
            elements: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfolding
        source = Expr::Unfolding(Unfolding {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ],
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            permission: PermAmount::Write,
            variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position,
        });
        expected = Expr::Unfolding(Unfolding {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position,
            })),
            permission: PermAmount::Write,
            variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Cond
        source = Expr::Cond(Cond {
            guard: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            then_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            else_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::Cond(Cond {
            guard: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            then_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            else_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ForAll
        source = Expr::ForAll(ForAll {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
            ],
            triggers: vec![Trigger::new(vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ])],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::ForAll(ForAll {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            triggers: vec![Trigger::new(vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ])],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Exists
        source = Expr::Exists(Exists {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
            ],
            triggers: vec![Trigger::new(vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ])],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::Exists(Exists {
            variables: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            triggers: vec![Trigger::new(vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ])],
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // LetExpr
        source = Expr::LetExpr(LetExpr {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
            def: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            position,
        });
        expected = Expr::LetExpr(LetExpr {
            variable: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            def: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            body: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // FuncApp
        source = Expr::FuncApp(FuncApp {
            function_name: String::from("f1"),
            type_arguments: vec![],
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
            ],
            formal_arguments: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::type_var("E"),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("T"),
                },
            ],
            return_type: Type::type_var("E"),
            position,
        });
        expected = Expr::FuncApp(FuncApp {
            function_name: String::from("f1"),
            type_arguments: vec![],
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
            ],
            formal_arguments: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
            ],
            return_type: Type::Bool,
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // DomainFuncApp
        source = Expr::DomainFuncApp(DomainFuncApp {
            domain_function: DomainFunc {
                name: String::from("df1"),
                type_arguments: vec![],
                formal_args: vec![
                    LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                ],
                return_type: Type::type_var("T"),
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
            ],
            position,
        });
        expected = Expr::DomainFuncApp(DomainFuncApp {
            domain_function: DomainFunc {
                name: String::from("df1"),
                type_arguments: vec![],
                formal_args: vec![
                    LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                ],
                return_type: Type::Int,
                unique: false,
                domain_name: String::from("dn1"),
            },
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
            ],
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // InhaleExhale
        source = Expr::InhaleExhale(InhaleExhale {
            inhale_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            exhale_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            position,
        });
        expected = Expr::InhaleExhale(InhaleExhale {
            inhale_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            exhale_expr: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = Expr::Downcast(DowncastExpr {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
            enum_place: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
            field: Field {
                name: String::from("f1"),
                typ: Type::type_var("E"),
            },
        });
        expected = Expr::Downcast(DowncastExpr {
            base: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            })),
            enum_place: Box::new(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            })),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Stmt, going over all variants
    fn substitution_type_var_stmt_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Comment
        let mut source = Stmt::Comment(Comment {
            comment: String::from("c1"),
        });
        let mut expected = Stmt::Comment(Comment {
            comment: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Label
        source = Stmt::Label(Label {
            label: String::from("c1"),
        });
        expected = Stmt::Label(Label {
            label: String::from("c1"),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Inhale
        source = Stmt::Inhale(Inhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
        });
        expected = Stmt::Inhale(Inhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Exhale
        source = Stmt::Exhale(Exhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            position,
        });
        expected = Stmt::Exhale(Exhale {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Assert
        source = Stmt::Assert(Assert {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            position,
        });
        expected = Stmt::Assert(Assert {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // MethodCall
        source = Stmt::MethodCall(MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
            ],
            targets: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::type_var("E"),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("T"),
                },
            ],
        });
        expected = Stmt::MethodCall(MethodCall {
            method_name: String::from("m1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
            ],
            targets: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Assign
        source = Stmt::Assign(Assign {
            target: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("E"),
                },
                position,
            }),
            source: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            kind: AssignKind::SharedBorrow(Borrow(123)),
        });
        expected = Stmt::Assign(Assign {
            target: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Bool,
                },
                position,
            }),
            source: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Int,
                },
                position,
            }),
            kind: AssignKind::SharedBorrow(Borrow(123)),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Fold
        source = Stmt::Fold(Fold {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position,
        });
        expected = Stmt::Fold(Fold {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Unfold
        source = Stmt::Unfold(Unfold {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
        });
        expected = Stmt::Unfold(Unfold {
            predicate: Type::typed_ref("p1"),
            arguments: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v2"),
                        typ: Type::Bool,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
            ],
            permission: PermAmount::Write,
            enum_variant: Some(EnumVariantIndex::new(String::from("evi"))),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Obtain
        source = Stmt::Obtain(Obtain {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            position,
        });
        expected = Stmt::Obtain(Obtain {
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // BeinFrame
        source = Stmt::BeginFrame(BeginFrame {});
        expected = Stmt::BeginFrame(BeginFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // EndFrame
        source = Stmt::EndFrame(EndFrame {});
        expected = Stmt::EndFrame(EndFrame {});
        test(source, expected, &SUBSTITUTION_MAP);

        // TransferPerm
        source = Stmt::TransferPerm(TransferPerm {
            left: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            right: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            }),
            unchecked: true,
        });
        expected = Stmt::TransferPerm(TransferPerm {
            left: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            right: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            }),
            unchecked: true,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // PackageMagicWand
        source = Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            package_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    position,
                }),
            ],
            label: String::from("l1"),
            variables: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("E"),
                },
            ],
            position,
        });
        expected = Stmt::PackageMagicWand(PackageMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            package_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    position,
                }),
            ],
            label: String::from("l1"),
            variables: vec![
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Bool,
                },
            ],
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ApplyMagicWand
        source = Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            position,
        });
        expected = Stmt::ApplyMagicWand(ApplyMagicWand {
            magic_wand: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            position,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // ExpireBorrows TODO: add this after DAG is checked
        source = Stmt::ExpireBorrows(ExpireBorrows {
            dag: DAG {
                borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
                nodes: vec![Node {
                    guard: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    borrow: Borrow(123),
                    reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                    reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            expr: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::type_var("T"),
                                },
                                position,
                            }),
                            position,
                        }),
                        Stmt::Obtain(Obtain {
                            expr: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::type_var("E"),
                                },
                                position,
                            }),
                            position,
                        }),
                    ],
                    borrowed_places: vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::type_var("E"),
                            },
                            position,
                        }),
                    ],
                    conflicting_borrows: vec![Borrow(403), Borrow(404)],
                    alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                    place: Some(Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    })),
                }],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v8"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                ],
            },
        });
        expected = Stmt::ExpireBorrows(ExpireBorrows {
            dag: DAG {
                borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
                nodes: vec![Node {
                    guard: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    borrow: Borrow(123),
                    reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                    reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                    stmts: vec![
                        Stmt::Obtain(Obtain {
                            expr: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v2"),
                                    typ: Type::Int,
                                },
                                position,
                            }),
                            position,
                        }),
                        Stmt::Obtain(Obtain {
                            expr: Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::Bool,
                                },
                                position,
                            }),
                            position,
                        }),
                    ],
                    borrowed_places: vec![
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::Int,
                            },
                            position,
                        }),
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Bool,
                            },
                            position,
                        }),
                    ],
                    conflicting_borrows: vec![Borrow(403), Borrow(404)],
                    alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                    place: Some(Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position,
                    })),
                }],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v8"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                ],
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // If
        source = Stmt::If(If {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            then_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    position,
                }),
            ],
            else_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    position,
                }),
            ],
        });
        expected = Stmt::If(If {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            then_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    position,
                }),
            ],
            else_stmts: vec![
                Stmt::Inhale(Inhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                }),
                Stmt::Exhale(Exhale {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    position,
                }),
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Downcast
        source = Stmt::Downcast(Downcast {
            base: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
        });
        expected = Stmt::Downcast(Downcast {
            base: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
        });
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within BodylessMethod
    fn substitution_type_var_bodyless_method_test() {
        let source = BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("D"),
                },
            ],
            formal_returns: vec![LocalVar {
                name: String::from("_r"),
                typ: Type::typed_ref_with_args(
                    "CustomStruct",
                    vec![Type::type_var("E"), Type::type_var("F")],
                ),
            }],
        };

        let expected = BodylessMethod {
            name: String::from("bm1"),
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("D"),
                },
            ],
            formal_returns: vec![LocalVar {
                name: String::from("_r"),
                typ: Type::typed_ref_with_args(
                    "CustomStruct",
                    vec![Type::Bool, Type::typed_ref("SimpleRef")],
                ),
            }],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DomainFunc
    fn substitution_type_var_domain_func_test() {
        let source = DomainFunc {
            name: String::from("df"),
            type_arguments: vec![],
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("D"),
                },
            ],
            return_type: Type::type_var("T"),
            unique: true,
            domain_name: String::from("dn"),
        };

        let expected = DomainFunc {
            name: String::from("df"),
            type_arguments: vec![],
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("D"),
                },
            ],
            return_type: Type::Int,
            unique: true,
            domain_name: String::from("dn"),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DomainAxiom
    fn substitution_type_var_domain_axiom_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = DomainAxiom {
            name: String::from("da"),
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            domain_name: String::from("dn"),
        };

        let expected = DomainAxiom {
            name: String::from("da"),
            expr: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            domain_name: String::from("dn"),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Domain
    fn substitution_type_var_domain_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Domain {
            name: String::from("domain"),
            functions: vec![
                DomainFunc {
                    name: String::from("df1"),
                    type_arguments: vec![],
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("D"),
                        },
                    ],
                    return_type: Type::type_var("T"),
                    unique: true,
                    domain_name: String::from("dn1"),
                },
                DomainFunc {
                    name: String::from("df2"),
                    type_arguments: vec![],
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("C"),
                        },
                    ],
                    return_type: Type::type_var("E"),
                    unique: true,
                    domain_name: String::from("dn2"),
                },
            ],
            axioms: vec![
                DomainAxiom {
                    name: String::from("da1"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    domain_name: String::from("dn3"),
                },
                DomainAxiom {
                    name: String::from("da2"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    domain_name: String::from("dn4"),
                },
            ],
            type_vars: vec![Type::type_var("T"), Type::type_var("E")],
        };

        let expected = Domain {
            name: String::from("domain"),
            functions: vec![
                DomainFunc {
                    name: String::from("df1"),
                    type_arguments: vec![],
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("D"),
                        },
                    ],
                    return_type: Type::Int,
                    unique: true,
                    domain_name: String::from("dn1"),
                },
                DomainFunc {
                    name: String::from("df2"),
                    type_arguments: vec![],
                    formal_args: vec![
                        LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("C"),
                        },
                    ],
                    return_type: Type::Bool,
                    unique: true,
                    domain_name: String::from("dn2"),
                },
            ],
            axioms: vec![
                DomainAxiom {
                    name: String::from("da1"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    domain_name: String::from("dn3"),
                },
                DomainAxiom {
                    name: String::from("da2"),
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    domain_name: String::from("dn4"),
                },
            ],
            type_vars: vec![Type::Int, Type::Bool],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Function
    fn substitution_type_var_function_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Function {
            name: String::from("f1"),
            type_arguments: vec![],
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            return_type: Type::type_var("T"),
            pres: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            posts: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Int,
                },
                position,
            })),
        };

        let expected = Function {
            name: String::from("f1"),
            type_arguments: vec![],
            formal_args: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            return_type: Type::Int,
            pres: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v3"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            posts: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Int,
                },
                position,
            })),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within StructPredicate
    fn substitution_type_var_struct_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = StructPredicate {
            typ: Type::typed_ref("sp1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::type_var("E"),
                },
                position,
            })),
        };

        let expected = StructPredicate {
            typ: Type::typed_ref("sp1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v7"),
                    typ: Type::Bool,
                },
                position,
            })),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within EnumPredicate
    fn substitution_type_var_enum_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = EnumPredicate {
            typ: Type::typed_ref("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::type_var("E"),
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("E"),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::type_var("E"),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        })),
                    },
                ),
            ],
        };

        let expected = EnumPredicate {
            typ: Type::typed_ref("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Int,
                            },
                            position,
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::Int,
                            },
                            position,
                        })),
                    },
                ),
            ],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Predicate, going over all variants
    fn substitution_type_var_predicate_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        // Struct
        let mut source = Predicate::Struct(StructPredicate {
            typ: Type::typed_ref("sp1"),
            this: LocalVar {
                name: String::from("_v4"),
                typ: Type::type_var("E"),
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
        });
        let mut expected = Predicate::Struct(StructPredicate {
            typ: Type::typed_ref("sp1"),
            this: LocalVar {
                name: String::from("_v4"),
                typ: Type::Bool,
            },
            body: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v5"),
                    typ: Type::Int,
                },
                position,
            })),
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Enum
        source = Predicate::Enum(EnumPredicate {
            typ: Type::typed_ref("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::type_var("E"),
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("E"),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::type_var("E"),
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        })),
                    },
                ),
            ],
        });
        expected = Predicate::Enum(EnumPredicate {
            typ: Type::typed_ref("ep1"),
            this: LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
            discriminant_field: Field {
                name: String::from("f1"),
                typ: Type::Bool,
            },
            discriminant_bounds: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            }),
            variants: vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v5"),
                                typ: Type::Int,
                            },
                            position,
                        })),
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v6"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    String::from("variant1"),
                    StructPredicate {
                        typ: Type::typed_ref("sp1"),
                        this: LocalVar {
                            name: String::from("_v7"),
                            typ: Type::Bool,
                        },
                        body: Some(Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v8"),
                                typ: Type::Int,
                            },
                            position,
                        })),
                    },
                ),
            ],
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // Bodyless
        source = Predicate::Bodyless(
            Type::type_var("b1"),
            LocalVar {
                name: String::from("_v1"),
                typ: Type::type_var("T"),
            },
        );

        expected = Predicate::Bodyless(
            Type::type_var("b1"),
            LocalVar {
                name: String::from("_v1"),
                typ: Type::Int,
            },
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Trigger
    fn substitution_type_var_trigger_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Trigger::new(vec![
            Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
                position,
            }),
        ]);
        let expected = Trigger::new(vec![
            Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
                position,
            }),
        ]);
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within CfgBlockIndex
    fn substitution_type_var_cfg_block_index_test() {
        // dummy position for convenient copying
        let uuid = Uuid::new_v4();

        let source = CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        };
        let expected = CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Successor, going over all variants
    fn substitution_type_var_successor_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        // Undefined
        let mut source = Successor::Undefined;
        let mut expected = Successor::Undefined;
        test(source, expected, &SUBSTITUTION_MAP);

        // Return
        source = Successor::Return;
        expected = Successor::Return;
        test(source, expected, &SUBSTITUTION_MAP);

        // Goto
        source = Successor::Goto(CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        });
        expected = Successor::Goto(CfgBlockIndex {
            method_uuid: uuid,
            block_index: 123,
        });
        test(source, expected, &SUBSTITUTION_MAP);

        // GotoSwitch
        source = Successor::GotoSwitch(
            vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 1,
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 2,
                    },
                ),
            ],
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            },
        );
        expected = Successor::GotoSwitch(
            vec![
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 1,
                    },
                ),
                (
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 2,
                    },
                ),
            ],
            CfgBlockIndex {
                method_uuid: uuid,
                block_index: 123,
            },
        );
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within CfgBlock
    fn substitution_type_var_cfg_block_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        let source = CfgBlock {
            stmts: vec![
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    position,
                }),
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    position,
                }),
            ],
            successor: Successor::GotoSwitch(
                vec![
                    (
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        }),
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 1,
                        },
                    ),
                    (
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::type_var("E"),
                            },
                            position,
                        }),
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 2,
                        },
                    ),
                ],
                CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 123,
                },
            ),
        };
        let expected = CfgBlock {
            stmts: vec![
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v1"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    position,
                }),
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    position,
                }),
            ],
            successor: Successor::GotoSwitch(
                vec![
                    (
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::Int,
                            },
                            position,
                        }),
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 1,
                        },
                    ),
                    (
                        Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v4"),
                                typ: Type::Bool,
                            },
                            position,
                        }),
                        CfgBlockIndex {
                            method_uuid: uuid,
                            block_index: 2,
                        },
                    ),
                ],
                CfgBlockIndex {
                    method_uuid: uuid,
                    block_index: 123,
                },
            ),
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within CfgMethod
    fn substitution_type_var_cfg_method_test() {
        // dummy uuid and position for convenient copying
        let uuid = Uuid::new_v4();
        let position = Position::new(1, 2, 3);

        let source = CfgMethod {
            uuid,
            method_name: String::from("mn1"),
            formal_arg_count: 5,
            formal_returns: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::type_var("E"),
                },
            ],
            local_vars: vec![
                LocalVar {
                    name: String::from("_v3"),
                    typ: Type::type_var("T"),
                },
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::type_var("E"),
                },
            ],
            labels: vec![String::from("l1"), String::from("l2")]
                .into_iter()
                .collect(),
            reserved_labels: vec![String::from("rl1"), String::from("rl2")]
                .into_iter()
                .collect(),
            basic_blocks: vec![CfgBlock {
                stmts: vec![
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v1"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        }),
                        position,
                    }),
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v2"),
                                typ: Type::type_var("E"),
                            },
                            position,
                        }),
                        position,
                    }),
                ],
                successor: Successor::GotoSwitch(
                    vec![
                        (
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::type_var("T"),
                                },
                                position,
                            }),
                            CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 1,
                            },
                        ),
                        (
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::type_var("E"),
                                },
                                position,
                            }),
                            CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 2,
                            },
                        ),
                    ],
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 123,
                    },
                ),
            }],
            basic_blocks_labels: vec![String::from("bbl1"), String::from("bbl2")],
            fresh_var_index: 1,
            fresh_label_index: 2,
        };
        let expected = CfgMethod {
            uuid,
            method_name: String::from("mn1"),
            formal_arg_count: 5,
            formal_returns: vec![
                LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v2"),
                    typ: Type::Bool,
                },
            ],
            local_vars: vec![
                LocalVar {
                    name: String::from("_v3"),
                    typ: Type::Int,
                },
                LocalVar {
                    name: String::from("_v4"),
                    typ: Type::Bool,
                },
            ],
            labels: vec![String::from("l1"), String::from("l2")]
                .into_iter()
                .collect(),
            reserved_labels: vec![String::from("rl1"), String::from("rl2")]
                .into_iter()
                .collect(),
            basic_blocks: vec![CfgBlock {
                stmts: vec![
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v1"),
                                typ: Type::Int,
                            },
                            position,
                        }),
                        position,
                    }),
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v2"),
                                typ: Type::Bool,
                            },
                            position,
                        }),
                        position,
                    }),
                ],
                successor: Successor::GotoSwitch(
                    vec![
                        (
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v3"),
                                    typ: Type::Int,
                                },
                                position,
                            }),
                            CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 1,
                            },
                        ),
                        (
                            Expr::Local(Local {
                                variable: LocalVar {
                                    name: String::from("_v4"),
                                    typ: Type::Bool,
                                },
                                position,
                            }),
                            CfgBlockIndex {
                                method_uuid: uuid,
                                block_index: 2,
                            },
                        ),
                    ],
                    CfgBlockIndex {
                        method_uuid: uuid,
                        block_index: 123,
                    },
                ),
            }],
            basic_blocks_labels: vec![String::from("bbl1"), String::from("bbl2")],
            fresh_var_index: 1,
            fresh_label_index: 2,
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within Node
    fn substitution_type_var_node_test() {
        // dummy position for convenient copying
        let position = Position::new(1, 2, 3);

        let source = Node {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::type_var("T"),
                },
                position,
            }),
            borrow: Borrow(123),
            reborrowing_nodes: vec![Borrow(1), Borrow(2)],
            reborrowed_nodes: vec![Borrow(1), Borrow(2)],
            stmts: vec![
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    position,
                }),
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                    position,
                }),
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ],
            conflicting_borrows: vec![Borrow(403), Borrow(404)],
            alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
            place: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v6"),
                    typ: Type::type_var("T"),
                },
                position,
            })),
        };

        let expected = Node {
            guard: Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v1"),
                    typ: Type::Int,
                },
                position,
            }),
            borrow: Borrow(123),
            reborrowing_nodes: vec![Borrow(1), Borrow(2)],
            reborrowed_nodes: vec![Borrow(1), Borrow(2)],
            stmts: vec![
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v2"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    position,
                }),
                Stmt::Obtain(Obtain {
                    expr: Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v3"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                    position,
                }),
            ],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v4"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v5"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
            conflicting_borrows: vec![Borrow(403), Borrow(404)],
            alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
            place: Some(Expr::Local(Local {
                variable: LocalVar {
                    name: String::from("_v6"),
                    typ: Type::Int,
                },
                position,
            })),
        };

        test(source, expected, &SUBSTITUTION_MAP);
    }

    #[test]
    // successful substitution within DAG
    fn substitution_type_var_dag_test() {
        // dummy position for convenient copying

        let position = Position::new(1, 2, 3);

        let source = DAG {
            borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
            nodes: vec![Node {
                guard: Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                borrow: Borrow(123),
                reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                stmts: vec![
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v2"),
                                typ: Type::type_var("T"),
                            },
                            position,
                        }),
                        position,
                    }),
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::type_var("E"),
                            },
                            position,
                        }),
                        position,
                    }),
                ],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::type_var("T"),
                        },
                        position,
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::type_var("E"),
                        },
                        position,
                    }),
                ],
                conflicting_borrows: vec![Borrow(403), Borrow(404)],
                alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                place: Some(Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::type_var("T"),
                    },
                    position,
                })),
            }],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v7"),
                        typ: Type::type_var("T"),
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v8"),
                        typ: Type::type_var("E"),
                    },
                    position,
                }),
            ],
        };

        let expected = DAG {
            borrow_indices: vec![(Borrow(1), 1), (Borrow(2), 2)].into_iter().collect(),
            nodes: vec![Node {
                guard: Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v1"),
                        typ: Type::Int,
                    },
                    position,
                }),
                borrow: Borrow(123),
                reborrowing_nodes: vec![Borrow(1), Borrow(2)],
                reborrowed_nodes: vec![Borrow(1), Borrow(2)],
                stmts: vec![
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v2"),
                                typ: Type::Int,
                            },
                            position,
                        }),
                        position,
                    }),
                    Stmt::Obtain(Obtain {
                        expr: Expr::Local(Local {
                            variable: LocalVar {
                                name: String::from("_v3"),
                                typ: Type::Bool,
                            },
                            position,
                        }),
                        position,
                    }),
                ],
                borrowed_places: vec![
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v4"),
                            typ: Type::Int,
                        },
                        position,
                    }),
                    Expr::Local(Local {
                        variable: LocalVar {
                            name: String::from("_v5"),
                            typ: Type::Bool,
                        },
                        position,
                    }),
                ],
                conflicting_borrows: vec![Borrow(403), Borrow(404)],
                alive_conflicting_borrows: vec![Borrow(1403), Borrow(1404)],
                place: Some(Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v6"),
                        typ: Type::Int,
                    },
                    position,
                })),
            }],
            borrowed_places: vec![
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v7"),
                        typ: Type::Int,
                    },
                    position,
                }),
                Expr::Local(Local {
                    variable: LocalVar {
                        name: String::from("_v8"),
                        typ: Type::Bool,
                    },
                    position,
                }),
            ],
        };
        test(source, expected, &SUBSTITUTION_MAP);
    }
}
