//! An adaptation of the example from
//! https://rosettacode.org/wiki/Dijkstra%27s_algorithm#Rust

extern crate prusti_contracts;

use std::cmp::Ordering;
use std::collections::BinaryHeap;
use std::usize;


struct VecWrapperNode{
    v: Vec<Node>
}

impl VecWrapperNode {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        Self { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: Node) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="after_expiry(self.len() == old(self.len()))"]
    pub fn borrow(&mut self, index: usize) -> &mut Node {
        self.v.get_mut(index).unwrap()
    }
}

struct VecWrapperWeightedEdge{
    v: Vec<WeightedEdge>
}

impl VecWrapperWeightedEdge {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        Self { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="forall i: usize :: (0 <= i && i < self.len()) ==> (
                    self.lookup_start(i) == old(self.lookup_start(i)) &&
                    self.lookup_end(i) == old(self.lookup_end(i)) &&
                    self.lookup_weight(i) == old(self.lookup_weight(i)))"]
    #[ensures="result.0 == self.lookup_start(index)"]
    #[ensures="result.1 == self.lookup_end(index)"]
    #[ensures="result.2 == self.lookup_weight(index)"]
    pub fn lookup(&mut self, index: usize) -> WeightedEdge {
        self.v[index]
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup_start(&self, index: usize) -> usize {
        self.v[index].0
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup_end(&self, index: usize) -> usize {
        self.v[index].1
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup_weight(&self, index: usize) -> usize {
        self.v[index].2
    }
}

struct VecWrapperUsizeUsize{
    v: Vec<(usize, usize)>
}

impl VecWrapperUsizeUsize {

    #[trusted]
    #[ensures="result.len() == 0"]
    pub fn new() -> Self {
        Self { v: Vec::new() }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: (usize, usize)) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="result.0 == old(self.lookup_target(index))"]
    #[ensures="after_expiry(self.len() == old(self.len()))"]
    pub fn borrow(&mut self, index: usize) -> &mut (usize, usize) {
        self.v.get_mut(index).unwrap()
    }

    #[trusted]
    #[pure]
    #[requires="0 <= index && index < self.len()"]
    pub fn lookup_target(&self, index: usize) -> usize {
        self.v[index].0
    }
}

struct VecWrapperPath{
    v: Vec<usize>
}

impl VecWrapperPath {

    #[trusted]
    #[requires="capacity >= 0"]
    #[ensures="result.len() == 0"]
    pub fn with_capacity(capacity: usize) -> Self {
        Self { v: Vec::with_capacity(capacity) }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: usize) {
        self.v.push(value);
    }

    #[trusted]
    pub fn reverse(&mut self) {
        self.v.reverse();
    }
}

struct VecWrapperDistances{
    v: Vec<(usize, Option<usize>)>
}

impl VecWrapperDistances {

    #[trusted]
    #[requires="0 <= length"]
    #[ensures="result.len() == length"]
    pub fn new(default: (usize, Option<usize>), length: usize) -> Self {
        Self {
            v: vec![default; length],
        }
    }

    #[trusted]
    #[pure]
    #[ensures="result >= 0"]
    pub fn len(&self) -> usize {
        self.v.len()
    }

    #[trusted]
    #[ensures="self.len() == old(self.len()) + 1"]
    pub fn push(&mut self, value: (usize, Option<usize>)) {
        self.v.push(value);
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    #[ensures="(match result {
                (_, Some(node)) => {
                    0 <= node && node < self.len()
                },
                (_, None) => true
    })"]
    pub fn lookup(&mut self, index: usize) -> (usize, Option<usize>) {
        self.v[index]
    }

    #[trusted]
    #[requires="0 <= index && index < self.len()"]
    #[ensures="self.len() == old(self.len())"]
    pub fn store(&mut self, index: usize, value: (usize, Option<usize>)) {
        self.v[index] = value;
    }
}

struct BinaryHeapWrapper {
    h: BinaryHeap<State>,
}

impl BinaryHeapWrapper {

    #[trusted]
    #[ensures="_ghost_node_count == result.node_count()"]
    pub fn new(_ghost_node_count: usize) -> Self {
        Self {
            h: BinaryHeap::new(),
        }
    }

    #[trusted]
    #[pure]
    pub fn node_count(&self) -> usize {
        unimplemented!();
    }

    #[trusted]
    #[requires="0 <= value.node && value.node < self.node_count()"]
    #[ensures="self.node_count() == old(self.node_count())"]
    pub fn push(&mut self, value: State) {
        self.h.push(value);
    }

    #[trusted]
    #[ensures="(match result {
        Some(State { node, .. }) => {
            0 <= node && node < self.node_count()
        },
        None => true
    })"]
    #[ensures="self.node_count() == old(self.node_count())"]
    pub fn pop(&mut self) -> Option<State> {
        self.h.pop()
    }
}

struct Grid {
    nodes: VecWrapperNode,
}

struct Node {
    data: char,
    edges: VecWrapperUsizeUsize,
}

#[derive(Copy, Clone, Eq, PartialEq)]
struct State {
    node: usize,
    cost: usize,
}

// Manually implement Ord so we get a min-heap instead of a max-heap
impl Ord for State {
    #[trusted]
    fn cmp(&self, other: &Self) -> Ordering {
        other.cost.cmp(&self.cost)
    }
}

impl PartialOrd for State {
    #[trusted]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

type WeightedEdge = (usize, usize, usize);

impl Grid {
    /*
    fn new() -> Self {
        Grid { nodes: VecWrapperNode::new() }
    }

    fn add_node(&mut self, data: char) -> usize {
        let node = Node {
            edges: VecWrapperUsizeUsize::new(),
            data: data,
        };
        self.nodes.push(node);
        self.nodes.len() - 1
    }

    #[requires="forall i: usize :: (0 <= i && i < vec.len()) ==> (
                    0 <= vec.lookup_start(i) && vec.lookup_start(i) < self.nodes.len() &&
                    0 <= vec.lookup_end(i) && vec.lookup_end(i) < self.nodes.len() &&
                    0 <= vec.lookup_weight(i))"]
    fn create_edges(&mut self, vec: &mut VecWrapperWeightedEdge) {
        let mut i = 0;
        let mut continue_loop = true;
        let mut continue_loop = i < vec.len();
        #[invariant="0 <= i"]
        #[invariant="continue_loop ==> i < vec.len()"]
        #[invariant="forall i: usize :: (0 <= i && i < vec.len()) ==> (
                        0 <= vec.lookup_start(i) && vec.lookup_start(i) < self.nodes.len() &&
                        0 <= vec.lookup_end(i) && vec.lookup_end(i) < self.nodes.len() &&
                        0 <= vec.lookup_weight(i))"]
        while continue_loop {
            let (start, end, weight) = vec.lookup(i);
            let start_node = self.nodes.borrow(start);
            start_node.edges.push((end, weight));
            let end_node = self.nodes.borrow(end);
            end_node.edges.push((start,weight));
            i += 1;
            continue_loop = i < vec.len();
        }
    }
    */

    #[requires="0 <= start && start < self.nodes.len()"]
    #[requires="0 <= end && end < self.nodes.len()"]
    fn find_path(&mut self, start: usize, end: usize) -> Option<(VecWrapperPath, usize)> {
        let mut dist = VecWrapperDistances::new((usize::MAX, None), self.nodes.len());

        let mut heap = BinaryHeapWrapper::new(self.nodes.len());
        dist.store(start, (0, None));
        heap.push(State {
            node: start,
            cost: 0,
        });

        let mut continue_loop = true;
        let mut result = None;
        #[invariant="heap.node_count() == self.nodes.len()"]
        #[invariant="dist.len() == self.nodes.len()"]
        #[invariant="0 <= end && end < self.nodes.len()"]
        while continue_loop {
            if let Some(State { node, cost }) = heap.pop() {
                if node == end {
                    let mut path = VecWrapperPath::with_capacity(dist.len() / 2);
                    let mut current_dist = dist.lookup(end);
                    path.push(end);
                    let mut continue_loop_1 = true;
                    #[invariant="(match current_dist {
                        (_, Some(node)) => {
                                0 <= node && node < dist.len()
                            },
                        (_, None) => true
                    })"]
                    while continue_loop_1 {
                        if let Some(prev) = current_dist.1 {
                            path.push(prev);
                            current_dist = dist.lookup(prev);
                        } else {
                            continue_loop_1 = false;
                        }
                    }
                    path.reverse();
                    result = Some((path, cost));
                    continue_loop = false;
                } else {
                    if !(cost > dist.lookup(node).0) {
                        let mut i = 0;
                        let node_count = self.nodes.len();
                        let borrowed_node = self.nodes.borrow(node);
                        let mut continue_loop_2 = i < borrowed_node.edges.len();
                        #[invariant="0 <= i && i <= borrowed_node.edges.len()"]
                        #[invariant="continue_loop_2 ==> i < borrowed_node.edges.len()"]
                        #[invariant="
                            forall k: usize ::
                            (0 <= k && k < borrowed_node.edges.len()) ==>
                            (0 <= borrowed_node.edges.lookup_target(k) &&
                             borrowed_node.edges.lookup_target(k) < node_count)
                        "]
                        #[invariant="node_count == dist.len()"]
                        #[invariant="node_count == heap.node_count()"]
                        while continue_loop_2 {
                            let edge = borrowed_node.edges.borrow(i);
                            let next = State {
                                node: edge.0,
                                cost: cost + edge.1,
                            };
                            if next.cost < dist.lookup(next.node).0 {
                                dist.store(next.node, (next.cost, Some(node)));
                                heap.push(next);
                            }
                            continue_loop_2 = i < borrowed_node.edges.len();
                        }
                        borrowed_node;
                            // TODO: This is a workaround for a bug,
                            // which we discovered after code freeze.
                    }
                }
            } else {
                continue_loop = false;
            }
        }
        result
    }
}

fn main() {
    /*
    let mut grid = Grid::new();
    let (a,b,c,d,e,f) = (grid.add_node("a"), grid.add_node("b"),
                         grid.add_node("c"), grid.add_node("d"),
                         grid.add_node("e"), grid.add_node("f"));

    grid.create_edges(&[
        (a,b,7) ,(a,c,9) ,(a,f,14),
        (b,c,10),(b,d,15),(c,d,11),
        (c,f,2) ,(d,e,6) ,(e,f,9) ,
    ]);

    let (path, cost) = grid.find_path(a,e).unwrap();

    print!("{}", grid.nodes[path[0]].data);
    for i in path.iter().skip(1) {
        print!(" -> {}", grid.nodes[*i].data);
    }
    println!("\nCost: {}", cost);
    */

}
