//! Balanced binary decomposition of a conformal submap's dual tree.
//!
//! Region IDs include empty regions. Chord IDs are positions in the supplied
//! edge array, not new IDs assigned by the decomposition.

use crate::work::Work;
use std::fmt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Node {
    Region(usize),
    Split {
        chord: usize,
        left: usize,
        right: usize,
    },
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Decomposition {
    pub nodes: Vec<Node>,
    pub root: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum DecompositionError {
    NoRegions,
    InvalidEndpoint { chord: usize, region: usize },
    SelfLoop { chord: usize, region: usize },
    NonConformal { region: usize, degree: usize },
    Cycle { chord: usize },
    Disconnected { reached: usize, region_count: usize },
}

impl fmt::Display for DecompositionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::NoRegions => write!(f, "a dual tree must contain at least one region"),
            Self::InvalidEndpoint { chord, region } => {
                write!(f, "chord {chord} has out-of-range region {region}")
            }
            Self::SelfLoop { chord, region } => {
                write!(f, "chord {chord} is a self-loop at region {region}")
            }
            Self::NonConformal { region, degree } => {
                write!(f, "region {region} has nonconformal degree {degree}")
            }
            Self::Cycle { chord } => write!(f, "chord {chord} closes a dual-graph cycle"),
            Self::Disconnected { reached, region_count } => {
                write!(f, "dual graph is disconnected: reached {reached} of {region_count} regions")
            }
        }
    }
}

impl std::error::Error for DecompositionError {}

impl Decomposition {
    /// Validate and decompose a degree-at-most-four tree in O(r log r + 1)
    /// region visits and O(r) auxiliary space. Validation itself is O(r).
    ///
    /// Every chord becomes exactly one split and every region exactly one leaf.
    /// Each child contains at most three quarters of its parent's chord count.
    /// Traversals of the input tree are iterative; only the balanced binary
    /// decomposition uses recursion. `work` includes visits made on errors.
    pub fn build(
        region_count: usize,
        chords: &[(usize, usize)],
        work: &mut Work,
    ) -> Result<Self, DecompositionError> {
        if region_count == 0 {
            return Err(DecompositionError::NoRegions);
        }
        // Fixed-size adjacency exploits conformality and avoids a heap allocation
        // for each region. Entries past `degree` are never read.
        let mut adjacency = vec![[0; 4]; region_count];
        let mut degree = vec![0usize; region_count];
        for (chord, &(a, b)) in chords.iter().enumerate() {
            for region in [a, b] {
                if region >= region_count {
                    return Err(DecompositionError::InvalidEndpoint { chord, region });
                }
            }
            if a == b {
                return Err(DecompositionError::SelfLoop { chord, region: a });
            }
            for region in [a, b] {
                if degree[region] == 4 {
                    return Err(DecompositionError::NonConformal { region, degree: 5 });
                }
                adjacency[region][degree[region]] = chord;
                degree[region] += 1;
            }
        }

        let mut parent = vec![usize::MAX; region_count];
        let mut order = Vec::with_capacity(region_count);
        parent[0] = 0;
        order.push(0);
        let mut cursor = 0;
        while cursor < order.len() {
            let region = order[cursor];
            cursor += 1;
            work.decomposition_visits += 1;
            for &chord in &adjacency[region][..degree[region]] {
                let (a, b) = chords[chord];
                let other = if a == region { b } else { a };
                // Skip only the exact discovery chord. Parallel chords must
                // remain visible to cycle detection.
                if region != 0 && chord == parent[region] {
                    continue;
                }
                if parent[other] != usize::MAX {
                    return Err(DecompositionError::Cycle { chord });
                }
                parent[other] = chord;
                order.push(other);
            }
        }
        if order.len() != region_count {
            return Err(DecompositionError::Disconnected {
                reached: order.len(),
                region_count,
            });
        }

        let mut builder = Builder {
            chords,
            adjacency,
            degree,
            parent,
            subtree: vec![0; region_count],
            order,
            blocked: vec![false; chords.len()],
            nodes: Vec::with_capacity(region_count),
            work,
        };
        let root = builder.component(0);
        Ok(Self { nodes: builder.nodes, root })
    }
}

struct Builder<'a> {
    chords: &'a [(usize, usize)],
    adjacency: Vec<[usize; 4]>,
    degree: Vec<usize>,
    // Discovery chords, shared by all recursive components.
    parent: Vec<usize>,
    subtree: Vec<usize>,
    order: Vec<usize>,
    blocked: Vec<bool>,
    nodes: Vec<Node>,
    work: &'a mut Work,
}

impl Builder<'_> {
    fn other(&self, chord: usize, region: usize) -> usize {
        let (a, b) = self.chords[chord];
        if a == region { b } else { a }
    }

    fn component(&mut self, seed: usize) -> usize {
        self.order.clear();
        self.order.push(seed);
        self.parent[seed] = usize::MAX;
        let mut cursor = 0;
        while cursor < self.order.len() {
            let region = self.order[cursor];
            cursor += 1;
            self.work.decomposition_visits += 1;
            self.subtree[region] = 1;
            for &chord in &self.adjacency[region][..self.degree[region]] {
                if self.blocked[chord] || self.parent[region] == chord {
                    continue;
                }
                let other = self.other(chord, region);
                self.parent[other] = chord;
                self.order.push(other);
            }
        }
        let node = self.nodes.len();
        self.nodes.push(Node::Region(seed));
        let size = self.order.len();
        if size == 1 {
            return node;
        }

        for index in (0..size).rev() {
            let region = self.order[index];
            self.work.decomposition_visits += 1;
            if self.parent[region] != usize::MAX {
                let parent = self.other(self.parent[region], region);
                self.subtree[parent] += self.subtree[region];
            }
        }

        let mut split = None;
        for &region in &self.order {
            self.work.decomposition_visits += 1;
            let mut largest = 0;
            let mut largest_chord = usize::MAX;
            for &chord in &self.adjacency[region][..self.degree[region]] {
                if self.blocked[chord] {
                    continue;
                }
                let branch_size = if chord == self.parent[region] {
                    size - self.subtree[region]
                } else {
                    self.subtree[self.other(chord, region)]
                };
                if branch_size > largest
                    || (branch_size == largest && chord < largest_chord)
                {
                    largest = branch_size;
                    largest_chord = chord;
                }
            }
            if largest <= size / 2 {
                split = Some(largest_chord);
                break;
            }
        }
        // Every nontrivial tree has a vertex centroid. At degree <= 4 its
        // largest branch has >= (size - 1)/4 vertices and <= size/2 vertices.
        // Cutting that branch thus leaves <= 3/4 of the old edges on each side.
        let chord = split.expect("validated nontrivial tree has a centroid");
        self.blocked[chord] = true;
        let (a, b) = self.chords[chord];
        // No per-component membership storage is retained across recursion:
        // blocked chords alone delimit components in the immutable input tree.
        let left = self.component(a);
        let right = self.component(b);
        self.nodes[node] = Node::Split { chord, left, right };
        node
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn check(region_count: usize, chords: &[(usize, usize)]) -> (usize, Work) {
        let mut work = Work::default();
        let decomposition = Decomposition::build(region_count, chords, &mut work).unwrap();
        assert_eq!(decomposition.nodes.len(), 2 * region_count - 1);
        let mut seen_regions = vec![false; region_count];
        let mut seen_chords = vec![false; chords.len()];
        let mut leaf_count = vec![0usize; decomposition.nodes.len()];
        let mut depth = vec![0usize; decomposition.nodes.len()];
        let mut traversal = vec![decomposition.root];
        let mut cursor = 0;
        while cursor < traversal.len() {
            let node = traversal[cursor];
            cursor += 1;
            match decomposition.nodes[node] {
                Node::Region(region) => {
                    assert!(!seen_regions[region]);
                    seen_regions[region] = true;
                    leaf_count[node] = 1;
                }
                Node::Split { chord, left, right } => {
                    assert!(!seen_chords[chord]);
                    seen_chords[chord] = true;
                    depth[left] = depth[node] + 1;
                    depth[right] = depth[node] + 1;
                    traversal.extend([left, right]);
                }
            }
        }
        for &node in traversal.iter().rev() {
            if let Node::Split { chord, left, right } = decomposition.nodes[node] {
                leaf_count[node] = leaf_count[left] + leaf_count[right];
                let old_edges = leaf_count[node] - 1;
                assert!(4 * (leaf_count[left] - 1) <= 3 * old_edges);
                assert!(4 * (leaf_count[right] - 1) <= 3 * old_edges);
                // Check the split's actual topology, not just its leaf counts.
                let mut left_regions = vec![false; region_count];
                let mut right_regions = vec![false; region_count];
                for (child, regions) in [(left, &mut left_regions), (right, &mut right_regions)] {
                    let mut pending = vec![child];
                    while let Some(child) = pending.pop() {
                        match decomposition.nodes[child] {
                            Node::Region(region) => regions[region] = true,
                            Node::Split { left, right, .. } => pending.extend([left, right]),
                        }
                    }
                }
                let (a, b) = chords[chord];
                assert!((left_regions[a] && right_regions[b])
                    || (left_regions[b] && right_regions[a]));
                for (other_chord, &(a, b)) in chords.iter().enumerate() {
                    if other_chord != chord {
                        assert!(!(left_regions[a] && right_regions[b]));
                        assert!(!(left_regions[b] && right_regions[a]));
                    }
                }
            }
        }
        assert!(seen_regions.into_iter().all(|seen| seen));
        assert!(seen_chords.into_iter().all(|seen| seen));
        (depth.into_iter().max().unwrap(), work)
    }

    #[test]
    fn single_empty_region_is_not_discarded() {
        let mut work = Work::default();
        let decomposition = Decomposition::build(1, &[], &mut work).unwrap();
        assert_eq!(decomposition.nodes, vec![Node::Region(0)]);
        assert_eq!(decomposition.root, 0);
        assert_eq!(work.decomposition_visits, 2);
    }

    #[test]
    fn paths_and_four_way_trees_obey_edge_balance() {
        for size in 2..80 {
            let path: Vec<_> = (1..size).map(|region| (region - 1, region)).collect();
            check(size, &path);
            let branching: Vec<_> = (1..size).map(|region| ((region - 1) / 3, region)).collect();
            check(size, &branching);
        }
        check(5, &[(0, 1), (0, 2), (0, 3), (0, 4)]);
    }

    #[test]
    fn long_path_has_logarithmic_depth_and_charged_work() {
        let size = 4097;
        let path: Vec<_> = (1..size).map(|region| (region - 1, region)).collect();
        // Avoid the intentionally exhaustive topology checks for the long path.
        let mut work = Work::default();
        let decomposition = Decomposition::build(size, &path, &mut work).unwrap();
        let mut pending = vec![(decomposition.root, 0usize)];
        let mut max_depth = 0;
        while let Some((node, depth)) = pending.pop() {
            max_depth = max_depth.max(depth);
            if let Node::Split { left, right, .. } = decomposition.nodes[node] {
                pending.extend([(left, depth + 1), (right, depth + 1)]);
            }
        }
        assert!(max_depth <= 14);
        assert!(work.decomposition_visits >= size as u128);
        assert!(work.decomposition_visits <= 4 * size as u128 * 15);
    }

    #[test]
    fn rejects_nonconformal_tree() {
        let mut work = Work::default();
        assert_eq!(
            Decomposition::build(6, &[(0, 1), (0, 2), (0, 3), (0, 4), (0, 5)], &mut work),
            Err(DecompositionError::NonConformal { region: 0, degree: 5 })
        );
    }

    #[test]
    fn rejects_bad_topology() {
        let mut work = Work::default();
        assert_eq!(Decomposition::build(0, &[], &mut work), Err(DecompositionError::NoRegions));
        assert_eq!(
            Decomposition::build(2, &[(0, 2)], &mut work),
            Err(DecompositionError::InvalidEndpoint { chord: 0, region: 2 })
        );
        assert_eq!(
            Decomposition::build(1, &[(0, 0)], &mut work),
            Err(DecompositionError::SelfLoop { chord: 0, region: 0 })
        );
        assert!(matches!(
            Decomposition::build(3, &[(0, 1), (1, 2), (2, 0)], &mut work),
            Err(DecompositionError::Cycle { .. })
        ));
        assert!(matches!(
            Decomposition::build(2, &[(0, 1), (0, 1)], &mut work),
            Err(DecompositionError::Cycle { .. })
        ));
        assert_eq!(
            Decomposition::build(3, &[(0, 1)], &mut work),
            Err(DecompositionError::Disconnected { reached: 2, region_count: 3 })
        );
    }
}
