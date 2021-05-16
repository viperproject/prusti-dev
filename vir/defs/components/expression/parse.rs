trait Interface {
    type Expression;
    fn parse_function_like(input: syn::parse::ParseStream) -> syn::Result<Expression>;
}

vir_raw_block! { kw =>
    pub mod kw {
        syn::custom_keyword!(forall);
        syn::custom_keyword!(exists);
    }
}

vir_raw_block! { Variable =>
    impl syn::parse::Parse for Variable {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let name = input.parse()?;
            Ok(Self { name })
        }
    }
    impl quote::ToTokens for Variable {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = self.name.to_string();
            tokens.extend(quote::quote! {
                Variable { name: #name.into() }
            })
        }
    }
}

vir_raw_block! { Constant =>
    impl syn::parse::Parse for Constant {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            Ok(Self {
                literal: input.parse()?,
            })
        }
    }
    impl quote::ToTokens for Constant {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let literal = &self.literal;
            tokens.extend(quote::quote! {
                #literal.into()
            })
        }
    }
}

vir_raw_block! { UnaryOperation =>
    impl syn::parse::Parse for UnaryOperation {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            Ok(UnaryOperation {
                kind: input.parse()?,
                arg: input.parse()?,
            })
        }
    }
    impl quote::ToTokens for UnaryOperation {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let kind = &self.kind;
            let arg = &self.arg;
            tokens.extend(quote::quote! {
                UnaryOperation {
                    kind: #kind, arg: Box::new(#arg)
                }
            })
        }
    }
}

vir_raw_block! { UnaryOperationKind =>
    impl syn::parse::Parse for UnaryOperationKind {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            if input.peek(syn::Token![-]) {
                input.parse::<syn::Token![-]>()?;
                Ok(UnaryOperationKind::Minus)
            } else {
                input.parse::<syn::Token![!]>()?;
                Ok(UnaryOperationKind::Not)
            }
        }
    }
    impl quote::ToTokens for UnaryOperationKind {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            match self {
                UnaryOperationKind::Not => tokens.extend(quote::quote! {UnaryOperationKind::Not}),
                UnaryOperationKind::Minus => tokens.extend(quote::quote! {UnaryOperationKind::Minus}),
            }
        }
    }
}

vir_raw_block! { BinaryOperation =>
    impl quote::ToTokens for BinaryOperation {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let kind = &self.kind;
            let left = &self.left;
            let right = &self.right;
            tokens.extend(quote::quote! {
                BinaryOperation {
                    kind: #kind, left: Box::new(#left), right: Box::new(#right),
                }
            })
        }
    }
}

vir_raw_block! { BinaryOperationKind =>
    impl syn::parse::Parse for BinaryOperationKind {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            if input.peek(syn::Token![==]) {
                input.parse::<syn::Token![==]>()?;
                Ok(BinaryOperationKind::EqCmp)
            } else if input.peek(syn::Token![!=]) {
                input.parse::<syn::Token![!=]>()?;
                Ok(BinaryOperationKind::NeCmp)
            } else if input.peek(syn::Token![>=]) {
                input.parse::<syn::Token![>=]>()?;
                Ok(BinaryOperationKind::GeCmp)
            } else if input.peek(syn::Token![>]) {
                input.parse::<syn::Token![>]>()?;
                Ok(BinaryOperationKind::GtCmp)
            } else if input.peek(syn::Token![<=]) {
                input.parse::<syn::Token![<=]>()?;
                Ok(BinaryOperationKind::LeCmp)
            } else if input.peek(syn::Token![<]) {
                input.parse::<syn::Token![<]>()?;
                Ok(BinaryOperationKind::LtCmp)
            } else if input.peek(syn::Token![&&]) {
                input.parse::<syn::Token![&&]>()?;
                Ok(BinaryOperationKind::And)
            } else if input.peek(syn::Token![||]) {
                input.parse::<syn::Token![||]>()?;
                Ok(BinaryOperationKind::Or)
            } else if input.peek(syn::Token![->]) {
                input.parse::<syn::Token![->]>()?;
                Ok(BinaryOperationKind::Implies)
            } else if input.peek(syn::Token![+]) {
                input.parse::<syn::Token![+]>()?;
                Ok(BinaryOperationKind::Add)
            } else if input.peek(syn::Token![-]) {
                input.parse::<syn::Token![-]>()?;
                Ok(BinaryOperationKind::Sub)
            } else if input.peek(syn::Token![*]) {
                input.parse::<syn::Token![*]>()?;
                Ok(BinaryOperationKind::Mul)
            } else if input.peek(syn::Token![/]) {
                input.parse::<syn::Token![/]>()?;
                Ok(BinaryOperationKind::Div)
            } else {
                input.parse::<syn::Token![%]>()?;
                Ok(BinaryOperationKind::Mod)
            }
        }
    }
    impl quote::ToTokens for BinaryOperationKind {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            match self {
                BinaryOperationKind::EqCmp => tokens.extend(quote::quote! {BinaryOperationKind::EqCmp}),
                BinaryOperationKind::NeCmp => tokens.extend(quote::quote! {BinaryOperationKind::NeCmp}),
                BinaryOperationKind::GtCmp => tokens.extend(quote::quote! {BinaryOperationKind::GtCmp}),
                BinaryOperationKind::GeCmp => tokens.extend(quote::quote! {BinaryOperationKind::GeCmp}),
                BinaryOperationKind::LtCmp => tokens.extend(quote::quote! {BinaryOperationKind::LtCmp}),
                BinaryOperationKind::LeCmp => tokens.extend(quote::quote! {BinaryOperationKind::LeCmp}),
                BinaryOperationKind::Add => tokens.extend(quote::quote! {BinaryOperationKind::Add}),
                BinaryOperationKind::Sub => tokens.extend(quote::quote! {BinaryOperationKind::Sub}),
                BinaryOperationKind::Mul => tokens.extend(quote::quote! {BinaryOperationKind::Mul}),
                BinaryOperationKind::Div => tokens.extend(quote::quote! {BinaryOperationKind::Div}),
                BinaryOperationKind::Mod => tokens.extend(quote::quote! {BinaryOperationKind::Mod}),
                BinaryOperationKind::And => tokens.extend(quote::quote! {BinaryOperationKind::And}),
                BinaryOperationKind::Or => tokens.extend(quote::quote! {BinaryOperationKind::Or}),
                BinaryOperationKind::Implies => tokens.extend(quote::quote! {BinaryOperationKind::Implies}),
            }
        }
    }
}

vir_raw_block! { Conditional =>
    impl syn::parse::Parse for Conditional {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            input.parse::<syn::Token![if]>()?;
            let guard = input.parse()?;
            let then_content;
            syn::braced!(then_content in input);
            let then_expr = then_content.parse()?;
            if !then_content.is_empty() {
                return Err(syn::Error::new(then_content.span(), "Unexpected tokens"));
            }
            input.parse::<syn::Token![else]>()?;
            let else_content;
            syn::braced!(else_content in input);
            let else_expr = else_content.parse()?;
            if !else_content.is_empty() {
                return Err(syn::Error::new(else_content.span(), "Unexpected tokens"));
            }
            Ok(Self {
                guard,
                then_expr,
                else_expr,
            })
        }
    }
    impl quote::ToTokens for Conditional {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let guard = &self.guard;
            let then_expr = &self.then_expr;
            let else_expr = &self.else_expr;
            tokens.extend(quote::quote! {
                Conditional {
                    guard: Box::new(#guard),
                    then_expr: Box::new(#then_expr),
                    else_expr: Box::new(#else_expr),
                }
            })
        }
    }
}

vir_raw_block! { Quantifier =>
    impl syn::parse::Parse for Quantifier {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let kind = input.parse()?;
            let quantifier_content;
            syn::parenthesized!(quantifier_content in input);
            quantifier_content.parse::<syn::Token![|]>()?;
            let parsed_variables: syn::punctuated::Punctuated<BoundedVariableDecl, syn::Token![,]> =
            syn::punctuated::Punctuated::parse_separated_nonempty(&quantifier_content)?;
            let variables = parsed_variables.into_iter().collect();
            quantifier_content.parse::<syn::Token![|]>()?;
            let body = quantifier_content.parse()?;
            quantifier_content.parse::<syn::Token![,]>()?;
            let content;
            syn::bracketed!(content in quantifier_content);
            let parsed_triggers: syn::punctuated::Punctuated<_, syn::Token![,]> = content.parse_terminated(Trigger::parse)?;
            let triggers = parsed_triggers.into_iter().collect();
            if !quantifier_content.is_empty() {
                return Err(syn::Error::new(quantifier_content.span(), "Unexpected tokens"));
            }
            Ok(Self {
                kind,
                variables,
                body,
                triggers,
            })
        }
    }
    impl quote::ToTokens for Quantifier {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let kind = &self.kind;
            let mut variable_tokens = proc_macro2::TokenStream::new();
            for variable in &self.variables {
                variable_tokens.extend(quote::quote! { #variable, });
            }
            let mut trigger_tokens = proc_macro2::TokenStream::new();
            for trigger in &self.triggers {
                trigger_tokens.extend(quote::quote! { #trigger, });
            }
            let body = &self.body;
            tokens.extend(quote::quote! {
                {
                    let kind = #kind;
                    let variables = vec![#variable_tokens];
                    let triggers = vec![#trigger_tokens];
                    let body = Box::new(#body);
                    Quantifier {
                        kind,
                        variables,
                        triggers,
                        body,
                    }
                }
            });
        }
    }
}

vir_raw_block! { QuantifierKind =>
    impl syn::parse::Parse for QuantifierKind {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let kind = if input.peek(kw::forall) {
                input.parse::<kw::forall>()?;
                QuantifierKind::ForAll
            } else {
                input.parse::<kw::exists>()?;
                QuantifierKind::Exists
            };
            Ok(kind)
        }
    }
    impl quote::ToTokens for QuantifierKind {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            match self {
                QuantifierKind::ForAll => tokens.extend(quote::quote! {QuantifierKind::ForAll}),
                QuantifierKind::Exists => tokens.extend(quote::quote! {QuantifierKind::Exists}),
            }
        }
    }
}

vir_raw_block! { Trigger =>
    impl syn::parse::Parse for Trigger {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let content;
            syn::parenthesized!(content in input);
            let punctuated: syn::punctuated::Punctuated<_, syn::Token![,]> = content.parse_terminated(Expression::parse)?;
            Ok(Self {
                parts: punctuated.into_iter().collect(),
            })
        }
    }
    impl quote::ToTokens for Trigger {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let mut part_tokens = proc_macro2::TokenStream::new();
            for part in &self.parts {
                part_tokens.extend(quote::quote! { #part, });
            }
            tokens.extend(quote::quote! {
                {
                    let parts = vec![#part_tokens];
                    Trigger {
                        parts,
                    }
                }
            });
        }
    }
}

vir_raw_block! { BoundedVariableDecl =>
    impl syn::parse::Parse for BoundedVariableDecl {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let name = input.parse()?;
            input.parse::<syn::Token![:]>()?;
            let sort = input.parse()?;
            Ok(Self { name, sort })
        }
    }
    impl quote::ToTokens for BoundedVariableDecl {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let name = self.name.to_string();
            let sort = &self.sort;
            tokens.extend(quote::quote! {
                BoundedVariableDecl {
                    name: #name.into(),
                    sort: #sort,
                }
            });
        }
    }
}

vir_raw_block! { FunctionApplication =>
    impl syn::parse::Parse for FunctionApplication {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            let function = input.parse()?;
            let content;
            syn::parenthesized!(content in input);
            let punctuated: syn::punctuated::Punctuated<_, syn::Token![,]> = content.parse_terminated(Expression::parse)?;
            let args = punctuated.into_iter().collect();
            Ok(Self { function, args })
        }
    }
    impl quote::ToTokens for FunctionApplication {
        fn to_tokens(&self, tokens: &mut proc_macro2::TokenStream) {
            let function = &self.function;
            let mut arg_tokens = proc_macro2::TokenStream::new();
            for arg in &self.args {
                arg_tokens.extend(quote::quote! { #arg, });
            }
            tokens.extend(quote::quote! {
                {
                    let function = #function;
                    let args = vec![#arg_tokens];
                    Quantifier {
                        function,
                        args,
                    }
                }
            });
        }
    }
}

vir_raw_block! { Expression =>
    #[derive(Debug, PartialEq, Eq, PartialOrd, Ord)]
    pub enum Precedence {
        Any,
        Implies,
        And,
        Compare,
        Add,
        Mul,
    }
    impl BinaryOperationKind {
        pub fn precedence(&self) -> Precedence {
            match self {
                BinaryOperationKind::EqCmp => Precedence::Compare,
                BinaryOperationKind::NeCmp => Precedence::Compare,
                BinaryOperationKind::GtCmp => Precedence::Compare,
                BinaryOperationKind::GeCmp => Precedence::Compare,
                BinaryOperationKind::LtCmp => Precedence::Compare,
                BinaryOperationKind::LeCmp => Precedence::Compare,
                BinaryOperationKind::Add => Precedence::Add,
                BinaryOperationKind::Sub => Precedence::Add,
                BinaryOperationKind::Mul => Precedence::Mul,
                BinaryOperationKind::Div => Precedence::Mul,
                BinaryOperationKind::Mod => Precedence::Mul,
                BinaryOperationKind::And => Precedence::And,
                BinaryOperationKind::Or => Precedence::And,
                BinaryOperationKind::Implies => Precedence::Implies,
            }
        }
    }
    fn trailer_expression(input: syn::parse::ParseStream) -> syn::Result<Expression> {
        if input.peek2(syn::token::Paren) {
            parse_function_like(input)
        } else if input.peek(syn::Lit) {
            // Must be a literal.
            Ok(Expression::Constant(input.parse()?))
        } else if input.peek(syn::token::Paren) {
            let content;
            syn::parenthesized!(content in input);
            content.parse()
        } else if input.peek(syn::Token![#]) {
            input.parse::<syn::Token![#]>()?;
            Ok(Expression::Hole(input.parse()?))
        } else {
            Ok(Expression::Variable(input.parse()?))
        }
    }
    fn unary_expression(input: syn::parse::ParseStream) -> syn::Result<Expression> {
        if input.peek(syn::Token![if]) {
            Ok(Expression::Conditional(input.parse()?))
        } else if input.peek(syn::Token![!]) || input.peek(syn::Token![-]) {
            Ok(Expression::UnaryOperation(UnaryOperation {
                kind: input.parse()?,
                arg: Box::new(unary_expression(input)?),
            }))
        } else {
            trailer_expression(input)
        }
    }
    fn peek_precedence(input: syn::parse::ParseStream) -> Precedence {
        if let Ok(kind) = input.fork().parse::<BinaryOperationKind>() {
            kind.precedence()
        } else {
            Precedence::Any
        }
    }
    fn do_parse_expression(
        input: syn::parse::ParseStream,
        mut lhs: Expression,
        base: Precedence,
    ) -> syn::Result<Expression> {
        loop {
            if input
                .fork()
                .parse::<BinaryOperationKind>()
                .ok()
                .map_or(false, |kind| kind.precedence() >= base)
            {
                let kind: BinaryOperationKind = input.parse()?;
                let precedence = kind.precedence();
                let mut rhs = unary_expression(input)?;
                loop {
                    let next = peek_precedence(input);
                    if next > precedence {
                        rhs = do_parse_expression(input, rhs, next)?;
                    } else {
                        break;
                    }
                }
                lhs = Expression::BinaryOperation(BinaryOperation {
                    kind,
                    left: Box::new(lhs),
                    right: Box::new(rhs),
                });
            } else {
                break;
            }
        }
        Ok(lhs)
    }
    fn parse_expression(input: syn::parse::ParseStream) -> syn::Result<Expression> {
        let lhs = unary_expression(input)?;
        do_parse_expression(input, lhs, Precedence::Any)
    }
    impl syn::parse::Parse for Expression {
        fn parse(input: syn::parse::ParseStream) -> syn::Result<Self> {
            parse_expression(input)
        }
    }
}
