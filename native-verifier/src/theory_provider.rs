pub struct ContainerTheoryProvider<'a> {
    template: &'a str,
}

impl ContainerTheoryProvider<'_> {
    pub fn new(theory: &str) -> Self {
        let template = match theory {
            "Set" => include_str!("theories/Set.smt2"),
            "MultiSet" => include_str!("theories/MultiSet.smt2"),
            "Seq" => include_str!("theories/Seq.smt2"),
            _ => panic!("Theory {} not supported", theory),
        };
        Self { template }
    }

    pub fn get_theory(&self, element_type: &str) -> String {
        self.template.replace("TYPENAME", element_type)
    }
}

pub struct MapTheoryProvider<'a> {
    template: &'a str,
}

impl MapTheoryProvider<'_> {
    pub fn new() -> Self {
        let template = include_str!("theories/Map.smt2");
        Self { template }
    }

    pub fn get_theory(&self, key_type: &str, value_type: &str) -> String {
        self.template
            .replace("KEYTYPE", key_type)
            .replace("VALUETYPE", value_type)
    }
}
