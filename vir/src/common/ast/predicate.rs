#[macro_export]
macro_rules! enum_predicate {
    ($self: ident) => {{
        let discriminant_loc =
            Expr::from($self.this.clone()).field($self.discriminant_field.clone());
        let discriminant_perm = Expr::acc_permission(discriminant_loc, PermAmount::Write);
        let mut parts = vec![discriminant_perm, $self.discriminant_bounds.clone()];
        // pred_perms is encoded as a conditional because each discriminant
        // guard is guaranteed to be mutually exclusive. In principle this
        // should enable more efficient verification compared to encoding the
        // enumeration as a disjunction of implications.
        let mut pred_perms: Option<Expr> = None;
        for (guard, name, variant) in $self.variants.iter() {
            if variant.has_empty_body() {
                continue;
            }
            let field = Field::new(format!("enum_{}", name), variant.this.typ.clone());
            let location: Expr = Expr::from($self.this.clone()).field(field);
            let field_perm = Expr::acc_permission(location.clone(), PermAmount::Write);
            let pred_perm = variant.construct_access(location, PermAmount::Write);
            if let Some(other_perms) = pred_perms {
                pred_perms = Some(Expr::ite(guard.clone(), pred_perm, other_perms));
            } else {
                pred_perms = Some(pred_perm);
            }
            parts.push(field_perm);
        }
        if let Some(perms) = pred_perms {
            parts.push(perms);
        }

        parts.into_iter().conjoin()
    }};
}
