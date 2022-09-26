pub fn encode_identifier(ident: String) -> String {
    // Rule: the rhs must always have an even number of "$"
    ident
        .replace("::", "$$")
        .replace('#', "$sharp$")
        .replace('<', "$openang$")
        .replace('>', "$closeang$")
        .replace('(', "$openrou$")
        .replace(')', "$closerou$")
        .replace('[', "$opensqu$")
        .replace(']', "$closesqu$")
        .replace('{', "$opencur$")
        .replace('}', "$closecur$")
        .replace(',', "$comma$")
        .replace(';', "$semic$")
        .replace(' ', "$space$")
        .replace('&', "$amp$")
        .replace('*', "$star$")
}
