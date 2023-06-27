use vir_crate::{
    common::display,
    low::{self as vir_low},
};

#[derive(derive_more::Display, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
#[display(fmt = "{}{}", "display::condition!(*visited, \"\", \"!\")", label)]
pub struct BlockMarkerConditionElement {
    pub label: vir_low::Label,
    pub visited: bool,
}

#[derive(derive_more::Display, PartialEq, Eq, PartialOrd, Ord, Clone, Debug)]
#[display(fmt = "{}", "display::cjoin(elements)")]
pub struct BlockMarkerCondition {
    pub elements: Vec<BlockMarkerConditionElement>,
}

impl BlockMarkerCondition {
    pub fn visited_with_disambiguator(
        visited_label: vir_low::Label,
        disambiguator: Vec<vir_low::Label>,
    ) -> Self {
        let mut this = Self {
            elements: Vec::new(),
        };
        this.extend_with_visited_with_disambiguator(visited_label, disambiguator);
        this
    }

    pub fn extend_with_visited_with_disambiguator(
        &mut self,
        visited_label: vir_low::Label,
        disambiguator: Vec<vir_low::Label>,
    ) {
        self.elements.push(BlockMarkerConditionElement {
            label: visited_label,
            visited: true,
        });
        for label in disambiguator {
            self.elements.push(BlockMarkerConditionElement {
                visited: false,
                label,
            });
        }
    }
}
