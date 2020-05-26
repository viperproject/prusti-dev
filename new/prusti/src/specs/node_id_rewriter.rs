use log::trace;
use log_derive::logfn_inputs;
use prusti_macros::{visit_mut_enum, visit_mut_struct};
use rustc_ast::ast::*;
use rustc_ast::ptr::P;
use rustc_ast::tokenstream::DelimSpan;
use rustc_data_structures::thin_vec::ThinVec;
use rustc_span::source_map::Spanned;
use rustc_span::symbol::Ident;
use rustc_span::Span;
use std::collections::HashMap;

/// A visitor responsible for fixing the node ids after we rewrote the crate.
pub(crate) struct NodeIdRewriter {
    /// The current position in the crate.
    current_path: Vec<String>,
    /// Is currently collecting the NodeIds or rewriting them?
    is_collecting: bool,
    /// Node Id of each stored element.
    ids: HashMap<Vec<String>, NodeId>,
    /// Compilation errors that were found in the AST.
    compiler_errors: Vec<(String, Span)>,
}

impl NodeIdRewriter {
    pub fn new(is_collecting: bool) -> Self {
        Self {
            is_collecting: is_collecting,
            current_path: Vec::new(),
            ids: HashMap::new(),
            compiler_errors: Vec::new(),
        }
    }
    pub fn set_phase_rewrite(&mut self) {
        assert!(self.is_collecting);
        self.is_collecting = false;
    }
    pub fn get_compiler_errors(&mut self) -> &mut Vec<(String, Span)> {
        &mut self.compiler_errors
    }
}

impl std::fmt::Debug for NodeIdRewriter {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("NodeIdRewriter")
            .field("collecting", &self.is_collecting)
            .field("current_path", &self.current_path)
            .finish()
    }
}

impl MutVisitor for NodeIdRewriter {
    fn down(&mut self, component: String) {
        self.current_path.push(component);
    }
    fn up(&mut self) {
        self.current_path.pop();
    }
    #[logfn_inputs(Trace)]
    fn visit_id(&mut self, node_id: &mut NodeId) {
        if self.is_collecting {
            assert!(
                !self.ids.contains_key(&self.current_path),
                "duplicate path: {:?}",
                self.current_path
            );
            self.ids.insert(self.current_path.clone(), *node_id);
        } else {
            // Set the old id.
            if let Some(old_id) = self.ids.get(&self.current_path) {
                *node_id = *old_id;
            }
        }
    }
    fn visit_mac(&mut self, mac: &mut MacCall) {
        assert!(!self.is_collecting, "Unresolved macro?");
        // Most likely the procedural macro reported an error.
        match mac {
            MacCall {
                path: Path { span, segments },
                args,
                prior_type_ascription: None,
            } if segments
                .first()
                .map(|segment| segment.ident.to_string().starts_with("compile_error"))
                .unwrap_or(false) =>
            {
                match &mut **args {
                    MacArgs::Delimited(_, _, tokens) => {
                        self.compiler_errors.push((
                            rustc_ast_pretty::pprust::tts_to_string(tokens.to_owned()),
                            *span,
                        ));
                    }
                    _ => {
                        unimplemented!("Uknown macro: {:?}", mac);
                    }
                }
            }
            _ => {
                unimplemented!("Uknown macro: {:?}", mac);
            }
        }
    }
}

pub trait MutVisitor: Sized {
    fn down(&mut self, component: String);
    fn up(&mut self);
    visit_mut_struct!(Crate { module: visit_mod, attrs: _, span: _, proc_macros: _ });

    // fn visit_meta_list_item(&mut self, list_item: &mut NestedMetaItem) {
    //     noop_visit_meta_list_item(list_item, self);
    // }

    // fn visit_meta_item(&mut self, meta_item: &mut MetaItem) {
    //     noop_visit_meta_item(meta_item, self);
    // }

    visit_mut_struct!(UseTree {
        prefix: visit_path,
        kind: visit_use_tree_kind,
        span: visit_span
    });

    visit_mut_enum!(UseTreeKind {
        Simple(visit_ident_opt, visit_id, visit_id),
        Nested(visit_use_tree_kind_nested),
        Glob()
    });

    fn visit_use_tree_kind_nested(&mut self, items: &mut Vec<(UseTree, NodeId)>) {
        trace!("[enter] visit_use_tree_kind_nested");
        for (i, (tree, id)) in items.iter_mut().enumerate() {
            self.down(i.to_string());
            self.visit_use_tree(tree);
            self.visit_id(id);
            self.up();
        }
        trace!("[exit] visit_use_tree_kind_nested");
    }

    visit_mut_struct!(ForeignItem {
        ident: visit_ident,
        attrs: list(visit_attribute),
        id: visit_id,
        kind: visit_foreign_item_kind,
        vis: _,
        span: visit_span,
        tokens: _
    });

    visit_mut_enum!(ForeignItemKind {
        Static(visit_ty, _, visit_expr_opt2),
        Fn(_, visit_fn_sig, visit_generics, visit_block_opt2),
        TyAlias(_, visit_generics, list(visit_generic_bound), visit_ty_opt2),
        MacCall(visit_mac),
    });

    visit_mut_struct!(Item {
        ident: visit_ident,
        attrs: list(visit_attribute),
        id: visit_id,
        kind: visit_item_kind,
        vis: _,
        span: visit_span,
        tokens: _
    });

    visit_mut_struct!(FnHeader {
        unsafety: _,
        asyncness: visit_async,
        constness: _,
        ext: _
    });

    visit_mut_struct!(StructField {
        span: visit_span,
        ident: visit_ident_opt,
        vis: visit_visibility,
        id: visit_id,
        ty: visit_ty,
        attrs: list(visit_attribute),
        is_placeholder: _
    });

    visit_mut_enum!(ItemKind {
        ExternCrate(_),
        Use(visit_use_tree),
        Static(visit_ty, _, visit_expr_opt2),
        Const(_, visit_ty, visit_expr_opt2),
        Fn(_, visit_fn_sig, visit_generics, visit_block_opt2),
        Mod(visit_mod),
        ForeignMod(visit_foreign_mod),
        GlobalAsm(_),
        TyAlias(_, visit_generics, list(visit_generic_bound), visit_ty_opt2),
        Enum(visit_enum_def, visit_generics),
        Struct(visit_variant_data, visit_generics),
        Union(visit_variant_data, visit_generics),
        Impl {
            unsafety: _,
            polarity: _,
            defaultness: _,
            constness: _,
            generics: visit_generics,
            of_trait: visit_trait_ref_opt,
            self_ty: visit_ty,
            items: list(visit_assoc_item),
        },
        Trait(_, _, visit_generics, list(visit_generic_bound), list(visit_assoc_item)),
        TraitAlias(visit_generics, list(visit_generic_bound)),
        MacCall(visit_mac),
        MacroDef(visit_macro_def),
    });

    visit_mut_struct!(AssocItem {
        id: visit_id,
        ident: visit_ident,
        vis: visit_visibility,
        attrs: list(visit_attribute),
        kind: visit_assoc_item_kind,
        span: visit_span,
        tokens: _
    });

    visit_mut_enum!(AssocItemKind {
        Const(_, visit_ty, visit_expr_opt2),
        Fn(_, visit_fn_sig, visit_generics, visit_block_opt2),
        TyAlias(_, visit_generics, list(visit_generic_bound), visit_ty_opt2),
        MacCall(visit_mac),
    });

    visit_mut_struct!(FnDecl {
        inputs: list(visit_param),
        output: visit_fn_ret_ty
    });

    visit_mut_enum!(FnRetTy {
        Default(visit_span),
        Ty(visit_ty),
    });

    visit_mut_enum!(Async {
        Yes { span: _, closure_id: visit_id, return_impl_trait_id: visit_id },
        No()
    });

    visit_mut_struct!(Block {
        id: visit_id,
        stmts: list(visit_stmt),
        rules: _,
        span: visit_span
    });
    fn visit_block_opt2(&mut self, block: &mut Option<P<Block>>) {
        if let Some(block) = block {
            self.visit_block(block);
        }
    }

    visit_mut_struct!(Stmt {
        kind: visit_stmt_kind,
        span: visit_span,
        id: visit_id
    });

    visit_mut_enum!(StmtKind {
        Local(visit_local),
        Item(visit_item),
        Expr(visit_expr),
        Semi(visit_expr),
        Empty(),
        MacCall(visit_mac_call)
    });

    fn visit_mac_call(&mut self, mac_call: &mut (MacCall, MacStmtStyle, ThinVec<Attribute>)) {
        let (mac, _semi, attrs) = mac_call;
        self.visit_mac(mac);
        for attr in attrs.iter_mut() {
            self.visit_attribute(attr);
        }
    }

    visit_mut_struct!(Arm {
        attrs: list(visit_attribute),
        pat: visit_pat,
        guard: visit_expr_opt2,
        body: visit_expr,
        span: visit_span,
        id: visit_id,
        is_placeholder: _
    });

    visit_mut_struct!(Pat {
        id: visit_id,
        kind: visit_pat_kind,
        span: visit_span
    });
    fn visit_pat_opt2(&mut self, pat: &mut Option<P<Pat>>) {
        if let Some(pat) = pat {
            self.visit_pat(pat);
        }
    }
    visit_mut_enum!(PatKind {
        Wild(),
        Rest(),
        Ident(_, visit_ident, visit_pat_opt2),
        Lit(visit_expr),
        TupleStruct(visit_path, list(visit_pat)),
        Path(visit_q_self_opt, visit_path),
        Struct(visit_path, list(visit_field_pat), _),
        Box(visit_pat),
        Ref(visit_pat, _),
        Range(visit_expr_opt2, visit_expr_opt2, visit_spanned),
        Tuple(list(visit_pat)),
        Slice(list(visit_pat)),
        Or(list(visit_pat)),
        Paren(visit_pat),
        MacCall(visit_mac)
    });
    fn visit_spanned<T>(&mut self, spanned: &mut Spanned<T>) {
        self.visit_span(&mut spanned.span);
    }

    visit_mut_struct!(AnonConst {
        id: visit_id,
        value: visit_expr
    });

    visit_mut_struct!(Expr {
        kind: visit_expr_kind,
        id: visit_id,
        span: visit_span,
        attrs: list(visit_attribute)
    });
    visit_mut_enum!(ExprKind {
        Box(visit_expr),
        Array(list(visit_expr)),
        Repeat(visit_expr, visit_anon_const),
        Tup(list(visit_expr)),
        Call(visit_expr, list(visit_expr)),
        MethodCall(visit_path_segment, list(visit_expr)),
        Binary(_, visit_expr, visit_expr),
        Unary(_, visit_expr),
        Cast(visit_expr, visit_ty),
        Type(visit_expr, visit_ty),
        AddrOf(_, _, visit_expr),
        Let(visit_pat, visit_expr),
        If(visit_expr, visit_block, visit_expr_opt2),
        While(visit_expr, visit_block, visit_label_opt),
        ForLoop(visit_pat, visit_expr, visit_block, visit_label_opt),
        Loop(visit_block, visit_label_opt),
        Match(visit_expr, list(visit_arm)),
        Closure(_, visit_async, _, visit_fn_decl, visit_expr, visit_span),
        Block(visit_block, visit_label_opt),
        Async(_, visit_id, visit_block),
        Await(visit_expr),
        Assign(visit_expr, visit_expr, _),
        AssignOp(_, visit_expr, visit_expr),
        Field(visit_expr, visit_ident),
        Index(visit_expr, visit_expr),
        Range(visit_expr_opt2, visit_expr_opt2, _),
        Path(visit_q_self_opt, visit_path),
        Break(visit_label_opt, visit_expr_opt2),
        Continue(visit_label_opt),
        Ret(visit_expr_opt2),
        // InlineAsm(visit_asm), TODO
        LlvmInlineAsm(visit_llvm_inline_asm),
        MacCall(visit_mac),
        Struct(visit_path, list(visit_field), visit_expr_opt2),
        Paren(visit_expr),
        Yield(visit_expr_opt2),
        Try(visit_expr),
        TryBlock(visit_block),
        Lit(_),
        Err()
    });
    fn visit_expr_opt2(&mut self, expr: &mut Option<P<Expr>>) {
        if let Some(expr) = expr {
            self.visit_expr(expr);
        }
    }

    fn visit_llvm_inline_asm(&mut self, _asm: &mut LlvmInlineAsm) {
        unimplemented!("LLVM Inline ASM is not supported");
    }

    // fn filter_map_expr(&mut self, e: P<Expr>) -> Option<P<Expr>> {
    //     noop_filter_map_expr(e, self)
    // }

    visit_mut_enum!(GenericArg {
        Lifetime(visit_lifetime),
        Type(visit_ty),
        Const(visit_anon_const),
    });

    visit_mut_struct!(Ty {
        id: visit_id,
        kind: visit_ty_kind,
        span: visit_span
    });
    visit_mut_enum!(TyKind {
        Infer(),
        ImplicitSelf(),
        Err(),
        Never(),
        CVarArgs(),
        Slice(visit_ty),
        Ptr(visit_mut_ty),
        Rptr(visit_lifetime_opt, visit_mut_ty),
        BareFn(visit_bare_fn_ty),
        Tup(list(visit_ty)),
        Paren(visit_ty),
        Path(visit_q_self_opt, visit_path),
        Array(visit_ty, visit_anon_const),
        Typeof(visit_anon_const),
        TraitObject(list(visit_generic_bound), _),
        ImplTrait(visit_id, list(visit_generic_bound)),
        MacCall(visit_mac),
    });
    fn visit_ty_opt2(&mut self, ty: &mut Option<P<Ty>>) {
        if let Some(ty) = ty {
            self.visit_ty(ty);
        }
    }

    visit_mut_struct!(BareFnTy {
        unsafety: _,
        ext: _,
        generic_params: list(visit_generic_param),
        decl: visit_fn_decl
    });

    visit_mut_struct!(Lifetime {
        id: visit_id,
        ident: visit_ident
    });

    visit_mut_struct!(AssocTyConstraint {
        id: visit_id,
        ident: visit_ident,
        kind: visit_assoc_ty_constraint_kind,
        span: visit_span
    });

    visit_mut_enum!(AssocTyConstraintKind {
        Equality { ty: visit_ty },
        Bound { bounds: list(visit_generic_bound) }
    });

    visit_mut_struct!(Mod { inner: visit_span, items: list(visit_item), inline: _ });

    visit_mut_struct!(ForeignMod { abi: _, items: list(visit_foreign_item) });

    visit_mut_struct!(Variant {
        ident: visit_ident,
        vis: visit_visibility,
        attrs: list(visit_attribute),
        id: visit_id,
        data: visit_variant_data,
        disr_expr: visit_anon_const_opt,
        span: visit_span,
        is_placeholder: _
    });

    visit_mut_struct!(Ident { name: _, span: visit_span });

    visit_mut_struct!(Path {
        segments: list(visit_path_segment),
        span: visit_span
    });

    visit_mut_struct!(PathSegment {
        ident: visit_ident,
        id: visit_id,
        args: visit_generic_args_opt2
    });

    visit_mut_struct!(QSelf {
        ty: visit_ty,
        path_span: visit_span,
        position: _
    });

    visit_mut_enum!(GenericArgs {
        AngleBracketed(visit_angle_bracketed_args),
        Parenthesized(visit_parenthesized_args),
    });
    fn visit_generic_args_opt2(&mut self, args: &mut Option<P<GenericArgs>>) {
        if let Some(args) = args {
            self.visit_generic_args(args);
        }
    }

    visit_mut_struct!(AngleBracketedArgs {
        args: list(visit_angle_bracketed_arg),
        span: visit_span
    });

    visit_mut_enum!(AngleBracketedArg {
        Arg(visit_generic_arg),
        Constraint(visit_assoc_ty_constraint),
    });

    visit_mut_struct!(ParenthesizedArgs {
        inputs: list(visit_ty),
        output: visit_fn_ret_ty,
        span: visit_span
    });

    visit_mut_struct!(Local {
        id: visit_id,
        pat: visit_pat,
        ty: visit_ty_opt2,
        init: visit_expr_opt2,
        span: visit_span,
        attrs: list(visit_attribute)
    });

    fn visit_mac(&mut self, _mac: &mut MacCall) {
        panic!("visit_mac disabled by default");
    }

    visit_mut_struct!(MacroDef { body: visit_mac_args, macro_rules: _ });

    visit_mut_enum!(MacArgs {
        Empty(),
        Delimited(visit_delim_span, _, _),
        Eq(visit_span, _),
    });

    visit_mut_struct!(DelimSpan {
        open: visit_span,
        close: visit_span,
    });

    visit_mut_struct!(Label { ident: visit_ident });

    visit_mut_struct!(Attribute { kind: visit_attr_kind, id: _, style: _, span: visit_span });

    fn visit_attr_kind(&mut self, _kind: &mut AttrKind) {
        // Do nothing.
    }

    visit_mut_struct!(Param {
        attrs: list(visit_attribute),
        id: visit_id,
        pat: visit_pat,
        span: visit_span,
        ty: visit_ty,
        is_placeholder: _
    });

    visit_mut_struct!(Generics {
        params: list(visit_generic_param),
        where_clause: visit_where_clause,
        span: visit_span
    });

    visit_mut_struct!(TraitRef {
        path: visit_path,
        ref_id: visit_id
    });

    visit_mut_struct!(PolyTraitRef {
        bound_generic_params: list(visit_generic_param),
        trait_ref: visit_trait_ref,
        span: visit_span
    });

    visit_mut_struct!(EnumDef {
        variants: list(visit_variant)
    });

    visit_mut_enum!(VariantData {
        Struct(list(visit_struct_field), _),
        Tuple(list(visit_struct_field), visit_id),
        Unit(visit_id),
    });

    visit_mut_struct!(GenericParam {
        id: visit_id,
        ident: visit_ident,
        attrs: list(visit_attribute),
        bounds: list(visit_generic_bound),
        kind: visit_generic_param_kind,
        is_placeholder: _
    });
    visit_mut_enum!(GenericParamKind {
        Lifetime(),
        Type { default: visit_ty_opt2 },
        Const { ty: visit_ty },
    });

    // fn visit_tt(&mut self, tt: &mut TokenTree) {
    //     noop_visit_tt(tt, self);
    // }

    // fn visit_tts(&mut self, tts: &mut TokenStream) {
    //     noop_visit_tts(tts, self);
    // }

    // fn visit_token(&mut self, t: &mut Token) {
    //     noop_visit_token(t, self);
    // }

    // fn visit_interpolated(&mut self, nt: &mut token::Nonterminal) {
    //     noop_visit_interpolated(nt, self);
    // }

    visit_mut_enum!(GenericBound {
        Trait(visit_poly_trait_ref, _),
        Outlives(visit_lifetime)
    });

    visit_mut_struct!(MutTy { ty: visit_ty, mutbl: _ });

    visit_mut_struct!(Field {
        ident: visit_ident,
        expr: visit_expr,
        span: visit_span,
        is_shorthand: _,
        attrs: list(visit_attribute),
        id: visit_id,
        is_placeholder: _
    });

    visit_mut_struct!(WhereClause {
        predicates: list(visit_where_predicate),
        span: visit_span
    });

    visit_mut_enum!(WherePredicate {
        BoundPredicate(visit_where_bound_predicate),
        RegionPredicate(visit_where_region_predicate),
        EqPredicate(visit_where_eq_predicate)
    });

    visit_mut_struct!(WhereBoundPredicate {
        span: visit_span,
        bound_generic_params: list(visit_generic_param),
        bounded_ty: visit_ty,
        bounds: list(visit_generic_bound)
    });

    visit_mut_struct!(WhereRegionPredicate {
        span: visit_span,
        lifetime: visit_lifetime,
        bounds: list(visit_generic_bound)
    });

    visit_mut_struct!(WhereEqPredicate {
        id: visit_id,
        span: visit_span,
        lhs_ty: visit_ty,
        rhs_ty: visit_ty
    });

    visit_mut_struct!(Visibility {
        node: visit_visibility_kind,
        span: visit_span
    });
    visit_mut_enum!(VisibilityKind {
        Public(),
        Crate(_),
        Inherited(),
        Restricted { path: visit_path, id: visit_id },
    });

    fn visit_id(&mut self, _id: &mut NodeId) {
        // Do nothing.
    }

    fn visit_span(&mut self, _sp: &mut Span) {
        // Do nothing.
    }

    visit_mut_struct!(FieldPat {
        attrs: list(visit_attribute),
        id: visit_id,
        ident: visit_ident,
        is_placeholder: _,
        is_shorthand: _,
        pat: visit_pat,
        span: visit_span
    });

    visit_mut_struct!(FnSig {
        header: visit_fn_header,
        decl: visit_fn_decl
    });
}
