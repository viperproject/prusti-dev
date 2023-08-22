use std::collections::BTreeMap;
use vir_crate::typed::{self as vir_typed};

pub(in super::super) struct PlaceWithDeadLifetimes {
    pub(in super::super) place: vir_typed::Expression,
    pub(in super::super) lifetime: vir_typed::ty::LifetimeConst,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub(in super::super) struct Places {
    /// A map from a place with erased lifetimes to normal place. We need this
    /// because we do not take lifetimes into account when comparing.
    ///
    /// FIXME: Define an expression and type wrappers that when ordered do not
    /// take lifetimes and constants into account, so that we can use `BTreeSet`
    /// here and avoid many `clone()` (also in `has_prefix`).
    places: BTreeMap<vir_typed::Expression, vir_typed::Expression>,
}

impl Places {
    pub(in super::super) fn len(&self) -> usize {
        self.places.len()
    }

    pub(in super::super) fn is_empty(&self) -> bool {
        self.places.is_empty()
    }

    pub(in super::super) fn insert(&mut self, place: vir_typed::Expression) -> bool {
        self.places
            .insert(place.clone().erase_lifetime(), place)
            .is_none()
    }

    pub(in super::super) fn remove(&mut self, place: &vir_typed::Expression) -> bool {
        // FIXME: Avoid cloning.
        self.places
            .remove(&place.clone().erase_lifetime())
            .is_some()
    }

    pub(super) fn contains(&self, place: &vir_typed::Expression) -> bool {
        // FIXME: Avoid cloning.
        self.places.contains_key(&place.clone().erase_lifetime())
    }

    pub(super) fn iter(&self) -> impl Iterator<Item = &'_ vir_typed::Expression> {
        self.places.values()
    }

    pub(super) fn clear(&mut self) {
        self.places.clear()
    }

    pub(in super::super) fn drain_filter<'a, F>(
        &'a mut self,
        mut pred: F,
    ) -> impl Iterator<Item = vir_typed::Expression> + 'a
    where
        F: 'a + FnMut(&vir_typed::Expression) -> bool,
    {
        self.places
            .extract_if(move |_, place| pred(place))
            .map(|(_, place)| place)
    }
}

impl<'a> IntoIterator for &'a Places {
    type Item = &'a vir_typed::Expression;

    type IntoIter = Box<dyn Iterator<Item = Self::Item> + 'a>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.places.values())
    }
}

impl IntoIterator for Places {
    type Item = vir_typed::Expression;

    type IntoIter = Box<dyn Iterator<Item = Self::Item>>;

    fn into_iter(self) -> Self::IntoIter {
        Box::new(self.places.into_values())
    }
}
