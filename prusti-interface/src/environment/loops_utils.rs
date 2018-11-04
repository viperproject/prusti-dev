// This Source Code Form is subject to the terms of the Mozilla Public
// License, v. 2.0. If a copy of the MPL was not distributed with this
// file, You can obtain one at http://mozilla.org/MPL/2.0/.

use super::borrowck::facts;
use std::fmt;
use crate::utils;
use super::place_set::PlaceSet;
use rustc::mir;

#[derive(Clone, Copy, Debug)]
pub enum PermissionKind {
    /// Gives read permission to this node. It must not be a leaf node.
    ReadNode,
    /// Gives read permission to the entire subtree including this node.
    /// This must be a leaf node.
    ReadSubtree,
    /// Gives write permission to this node. It must not be a leaf node.
    WriteNode,
    /// Gives read permission to the entire subtree including this node.
    /// This must be a leaf node.
    WriteSubtree,
    /// Give no permission to this node and the entire subtree. This
    /// must be a leaf node.
    None,
}

impl PermissionKind {
    pub fn is_none(&self) -> bool {
        match self {
            PermissionKind::None => true,

            PermissionKind::ReadNode |
            PermissionKind::ReadSubtree |
            PermissionKind::WriteNode |
            PermissionKind::WriteSubtree => false,
        }
    }
}

#[derive(Debug)]
pub struct Loan<'tcx> {
    /// ID used in Polonius.
    id: facts::Loan,
    /// The location where the borrow starts.
    location: mir::Location,
    /// The borrowed place.
    place: mir::Place<'tcx>,
}

//#[derive(Clone, Copy, Debug)]
//enum BorrowKind {
//Shared,
//Mutable,
//}

#[derive(Debug)]
pub enum PermissionNode<'tcx> {
    OwnedNode {
        place: mir::Place<'tcx>,
        kind: PermissionKind,
        children: Vec<PermissionNode<'tcx>>,
    },
    // TODO: Make this the type only of the root node.
    BorrowedNode {
        place: mir::Place<'tcx>,
        kind: PermissionKind,
        child: Box<PermissionNode<'tcx>>,
        /// A list of locations from where this borrow may be borrowing.
        // TODO: Is this needed?
        may_borrow_from: Vec<Loan<'tcx>>,
    },
}

impl<'tcx> PermissionNode<'tcx> {

    pub fn get_place(&self) -> &mir::Place<'tcx> {
        match self {
            PermissionNode::OwnedNode { place, .. } => place,
            PermissionNode::BorrowedNode { place, .. } => place,
        }
    }

    pub fn set_permission_kind(&mut self, permission_kind: PermissionKind) {
        match self {
            PermissionNode::OwnedNode { ref mut kind, .. } => {
                *kind = permission_kind;
            },
            PermissionNode::BorrowedNode { .. } => {
                unimplemented!();
            },
        }
    }

    pub fn get_permission_kind(&self) -> PermissionKind {
        match self {
            PermissionNode::OwnedNode { kind, .. } |
            PermissionNode::BorrowedNode { kind, .. } => {
                *kind
            }
        }
    }

    pub fn get_or_create_child(&mut self, place: &mir::Place<'tcx>,
                               kind: PermissionKind) -> &mut Self {
        match self {
            PermissionNode::OwnedNode { children, .. } => {
                let index = children
                    .iter()
                    .position(|child| child.get_place() == place);
                if let Some(index) = index {
                    return &mut children[index];
                }
                let child = PermissionNode::OwnedNode {
                    place: place.clone(),
                    kind: kind,
                    children: Vec::new(),
                };
                children.push(child);
                let len = children.len();
                &mut children[len-1]
            },
            PermissionNode::BorrowedNode { .. } => {
                unimplemented!();   // TODO: Change code so that we do not
                // have to deal with this case.
            },
        }
    }

    pub fn get_children(&self) -> Vec<&PermissionNode<'tcx>> {
        match self {
            PermissionNode::OwnedNode { ref children, .. } => {
                children.iter().collect()
            }

            PermissionNode::BorrowedNode { box ref child, .. } => {
                vec![ child ]
            }
        }
    }
}

impl<'tcx> fmt::Display for PermissionNode<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        match self {
            PermissionNode::OwnedNode { place, kind, children } => {
                write!(f, "acc({:?}, {:?})", place, kind)?;
                for child in children.iter() {
                    write!(f, " && {}", child)?;
                }
            }
            PermissionNode::BorrowedNode { .. } => {
                unimplemented!();
            }
        }
        Ok(())
    }
}

#[derive(Debug)]
pub struct PermissionTree<'tcx> {
    root: PermissionNode<'tcx>,
}

impl<'tcx> PermissionTree<'tcx> {

    /// Create a permission tree such that:
    ///
    /// +   The `place` is of kind `WriteSubtree` or `ReadSubtree`
    ///     depending on `is_target_write`.
    /// +   All steps between `target_place` and `place` are of kind
    ///     `WriteNode` if `is_target_write`.
    /// +   All steps from the root until `target_place` are of kind
    ///     `ReadNode`.
    pub fn new(place: &mir::Place<'tcx>,
               target_place: &mir::Place<'tcx>,
               is_target_write: bool) -> Self {
        let place = utils::VecPlace::new(place);
        let mut place_iter = place.iter().rev();
        let node_permission_kind = if is_target_write {
            PermissionKind::WriteSubtree
        } else {
            PermissionKind::ReadSubtree
        };
        let mut node = PermissionNode::OwnedNode {
            place: place_iter.next().unwrap().get_mir_place().clone(),
            kind: node_permission_kind,
            children: Vec::new(),
        };
        let mut permission_kind = if node.get_place() == target_place || !is_target_write {
            PermissionKind::ReadNode
        } else {
            PermissionKind::WriteNode
        };
        while let Some(component) = place_iter.next() {
            node = PermissionNode::OwnedNode {
                place: component.get_mir_place().clone(),
                kind: permission_kind,
                children: vec![node],
            };
            if component.get_mir_place() == target_place {
                permission_kind = PermissionKind::ReadNode;
            }
        }
        Self { root: node, }
    }

    /// Add a new place by following the same rules as described in the
    /// comment for the `new`.
    pub fn add(&mut self,
               place: &mir::Place<'tcx>,
               _target_place: &mir::Place<'tcx>,
               is_target_write: bool) {
        let place = utils::VecPlace::new(place);
        let mut place_iter = place.iter();
        place_iter.next();  // Drop the root.
        debug!("place {:?}", place);
        debug!("self.root {:?}", self.root);
        let mut component_count = place.component_count() - 1;  // Without root.
        let mut current_parent_node = &mut self.root;
        while component_count > 1 {
            let component = place_iter.next().unwrap();
            component_count -= 1;
            let current_node = current_parent_node.get_or_create_child(
                component.get_mir_place(), PermissionKind::ReadNode);
            if is_target_write {
                current_node.set_permission_kind(PermissionKind::WriteNode);
            }
            current_parent_node = current_node;
        }
        let component = place_iter.next().unwrap();
        let kind = if is_target_write {
            PermissionKind::WriteSubtree
        } else {
            PermissionKind::ReadSubtree
        };
        let mut _current_node = current_parent_node.get_or_create_child(
            component.get_mir_place(), kind);
    }

    pub fn get_root_place(&self) -> &mir::Place {
        self.root.get_place()
    }

    pub fn get_root(&self) -> &PermissionNode<'tcx> {
        &self.root
    }

    pub fn get_nodes(&self) -> Vec<&PermissionNode<'tcx>> {
        let mut visited = vec![];
        let mut to_visit = vec![ &self.root ];
        while let Some(node) = to_visit.pop() {
            visited.push(node);
            for child in node.get_children().iter() {
                to_visit.push(child);
            }
        }
        visited
    }
}

impl<'tcx> fmt::Display for PermissionTree<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "{}", self.root)
    }
}

#[derive(Debug)]
pub struct PermissionForest<'tcx> {
    trees: Vec<PermissionTree<'tcx>>,
}

impl<'tcx> PermissionForest<'tcx> {
    /// +   `write_paths` – paths to whose leaves we should have write permission.
    /// +   `read_paths` – paths to whose leaves we should have read permission.
    pub fn new(write_paths: &Vec<mir::Place<'tcx>>, read_paths: &Vec<mir::Place<'tcx>>, all_places: &PlaceSet<'tcx>) -> Self {

        let mut trees: Vec<PermissionTree> = Vec::new();

        /// Take the intended place to add and compute the set of places
        /// to add that are definitely initialised.
        fn compute_places_to_add<'a, 'tcx>(place: &'a mir::Place<'tcx>,
                                           all_places: &'a PlaceSet<'tcx>
        ) -> Vec<(&'a mir::Place<'tcx>, &'a mir::Place<'tcx>)> {
            let mut found_def_init_prefix = false;
            let mut found_target_prefix = false;
            let mut result = Vec::new();
            for def_init_place in all_places.iter() {
                if utils::is_prefix(place, def_init_place) {
                    assert!(!found_target_prefix && !found_def_init_prefix);
                    result.push((place, place));
                    found_def_init_prefix = true;
                } else if utils::is_prefix(def_init_place, place) {
                    assert!(!found_def_init_prefix);
                    result.push((def_init_place, place));
                    found_target_prefix = true;
                }
            }
            assert!(found_target_prefix || found_def_init_prefix);
            result
        }

        /// Add places to the trees.
        fn add_paths<'tcx>(paths: &Vec<mir::Place<'tcx>>,
                           trees: &mut Vec<PermissionTree<'tcx>>,
                           is_write: bool,
                           all_places: &PlaceSet<'tcx>) {
            for place in paths.iter() {
                let mut found = false;
                let places_to_add = compute_places_to_add(place, all_places);
                for tree in trees.iter_mut() {
                    if utils::is_prefix(place, tree.get_root_place()) {
                        found = true;
                        for (actual_place, target_place) in places_to_add.iter() {
                            tree.add(actual_place, target_place, is_write);
                        }
                    }
                }
                if !found {
                    for (actual_place, target_place) in places_to_add.iter() {
                        let tree = PermissionTree::new(actual_place, target_place, is_write);
                        trees.push(tree);
                    }
                }
            }
        }
        add_paths(write_paths, &mut trees, true, all_places);
        add_paths(read_paths, &mut trees, false, all_places);
        Self {
            trees: trees,
        }
    }

    pub fn get_trees(&self) -> &[PermissionTree<'tcx>] {
        &self.trees
    }
}

impl<'tcx> fmt::Display for PermissionForest<'tcx> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let mut first = true;
        for tree in self.trees.iter() {
            if first {
                write!(f, "({})", tree.root)?;
                first = false;
            } else {
                write!(f, " && ({})", tree.root)?;
            }
        }
        Ok(())
    }
}
