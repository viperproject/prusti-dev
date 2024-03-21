// © 2019, ETH Zurich
//
// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

#[derive(Debug, Clone)]
pub struct ClassName {
    full_class_name_dot: String,
    full_class_name_slash: String,
    class_name: String,
}

impl ClassName {
    pub fn new(full_class_name: &str) -> Self {
        let full_class_name_dot = full_class_name.to_string().replace('/', ".");
        let full_class_name_slash = full_class_name_dot.replace('.', "/");
        let class_name = full_class_name_slash.split('/').last().unwrap().to_string();

        ClassName {
            full_class_name_dot,
            full_class_name_slash,
            class_name,
        }
    }

    pub fn name(&self) -> String {
        self.class_name.clone()
    }

    pub fn path(&self) -> String {
        self.full_class_name_slash.clone()
    }

    pub fn full_components(&self) -> Vec<&str> {
        self.full_class_name_slash.split('/').collect()
    }

    pub fn rust_name(&self) -> String {
        component_name_to_rust(&self.class_name)
    }

    pub fn full_rust_components(&self) -> Vec<String> {
        self.full_class_name_slash
            .split('/')
            .map(component_name_to_rust)
            .collect()
    }

    pub fn full_name(&self) -> String {
        self.full_class_name_dot.clone()
    }
}

fn component_name_to_rust(name: &str) -> String {
    name.replace('$', "_object")
}
