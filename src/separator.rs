//! Deterministic Lipton–Tarjan separation of a supplied spherical rotation system.
//!
//! The level selection, contraction, and nested fundamental-cycle search follow
//! Lipton and Tarjan, STAN-CS-77-627, §3. Face hubs are zero-cost leaves of the
//! spanning tree; they triangulate even faces whose boundary repeats a vertex.
//! Time and storage are O(V + E), including validation (O(V) for simple planar
//! graphs). The projected separator has at most sqrt(8 V) original vertices.
use crate::work::Work;
use std::fmt;

const NONE: usize = usize::MAX;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Dart {
    pub target: usize,
    pub twin: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EmbeddedGraph {
    pub darts: Vec<Dart>,
    pub rotations: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Separator {
    pub removed: Vec<usize>,
    pub components: Vec<Vec<usize>>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum SeparatorError {
    WeightCount,
    InvalidRotation,
    InvalidTwin,
    InvalidTarget,
    NonPlanarRotation,
}

impl fmt::Display for SeparatorError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(match self {
            Self::WeightCount => "weight count differs from vertex count",
            Self::InvalidRotation => "each dart must occur in exactly one vertex rotation",
            Self::InvalidTwin => "dart twins must be distinct reciprocal reverse darts",
            Self::InvalidTarget => "dart target is outside the vertex arena",
            Self::NonPlanarRotation => "rotation system is not spherical",
        })
    }
}
impl std::error::Error for SeparatorError {}

struct Embedding {
    owner: Vec<usize>,
    next: Vec<usize>,
    prev: Vec<usize>,
}

fn visit(work: &mut Work) {
    work.separator_visits += 1;
}

fn components(
    graph: &EmbeddedGraph,
    removed: &[bool],
    work: &mut Work,
) -> Vec<Vec<usize>> {
    let mut seen = removed.to_vec();
    let mut result = Vec::new();
    for start in 0..graph.rotations.len() {
        visit(work);
        if seen[start] {
            continue;
        }
        seen[start] = true;
        let mut component = vec![start];
        let mut head = 0;
        while head < component.len() {
            let v = component[head];
            head += 1;
            visit(work);
            for &d in &graph.rotations[v] {
                visit(work);
                let u = graph.darts[d].target;
                if !seen[u] {
                    seen[u] = true;
                    component.push(u);
                }
            }
        }
        result.push(component);
    }
    result
}

fn validate(graph: &EmbeddedGraph, work: &mut Work) -> Result<Embedding, SeparatorError> {
    let n = graph.rotations.len();
    let m = graph.darts.len();
    let mut owner = vec![NONE; m];
    let mut next = vec![NONE; m];
    let mut prev = vec![NONE; m];
    for (v, rotation) in graph.rotations.iter().enumerate() {
        visit(work);
        for (i, &d) in rotation.iter().enumerate() {
            visit(work);
            if d >= m || owner[d] != NONE {
                return Err(SeparatorError::InvalidRotation);
            }
            owner[d] = v;
            next[d] = rotation[(i + 1) % rotation.len()];
            prev[d] = rotation[(i + rotation.len() - 1) % rotation.len()];
        }
    }
    for (d, dart) in graph.darts.iter().enumerate() {
        visit(work);
        if owner[d] == NONE {
            return Err(SeparatorError::InvalidRotation);
        }
        if dart.target >= n {
            return Err(SeparatorError::InvalidTarget);
        }
        let t = dart.twin;
        if t >= m || t == d || graph.darts[t].twin != d
            || owner[t] != dart.target || graph.darts[t].target != owner[d]
        {
            return Err(SeparatorError::InvalidTwin);
        }
    }
    let parts = components(graph, &vec![false; n], work);
    let mut component_id = vec![NONE; n];
    let mut vertices = Vec::with_capacity(parts.len());
    for (c, part) in parts.iter().enumerate() {
        vertices.push(part.len());
        for &v in part {
            visit(work);
            component_id[v] = c;
        }
    }
    let mut edges = vec![0usize; parts.len()];
    let mut faces = vec![0usize; parts.len()];
    let mut seen = vec![false; m];
    for d in 0..m {
        visit(work);
        if d < graph.darts[d].twin {
            edges[component_id[owner[d]]] += 1;
        }
        if !seen[d] {
            faces[component_id[owner[d]]] += 1;
            let mut e = d;
            loop {
                visit(work);
                seen[e] = true;
                e = prev[graph.darts[e].twin];
                if e == d {
                    break;
                }
            }
        }
    }
    for c in 0..parts.len() {
        visit(work);
        // An isolated vertex has an empty face, not a dart orbit.
        if edges[c] == 0 {
            faces[c] = 1;
        }
        if vertices[c] + faces[c] != edges[c] + 2 {
            return Err(SeparatorError::NonPlanarRotation);
        }
    }
    Ok(Embedding { owner, next, prev })
}

impl Separator {
    pub fn build(
        graph: &EmbeddedGraph,
        weights: &[u64],
        work: &mut Work,
    ) -> Result<Self, SeparatorError> {
        let n = graph.rotations.len();
        if weights.len() != n {
            return Err(SeparatorError::WeightCount);
        }
        let embedding = validate(graph, work)?;
        let mut removed = vec![false; n];
        let parts = components(graph, &removed, work);
        let mut costs = Vec::with_capacity(parts.len());
        let mut total = 0u128;
        for part in &parts {
            let mut cost = 0;
            for &v in part {
                visit(work);
                cost += u128::from(weights[v]);
            }
            costs.push(cost);
            total += cost;
        }
        // Comparing against floor(2W/3) avoids overflow in 3*cost.
        let limit = total / 3 * 2 + (total % 3 * 2) / 3;
        let mut heavy = NONE;
        for (c, &cost) in costs.iter().enumerate() {
            visit(work);
            if cost > limit {
                heavy = c;
                break;
            }
        }
        if heavy != NONE {
            let part = &parts[heavy];
            let cost = costs[heavy];
            let mut heavy_vertex = NONE;
            for &v in part {
                visit(work);
                if u128::from(weights[v]) > cost / 3 {
                    heavy_vertex = v;
                    break;
                }
            }
            if heavy_vertex != NONE {
                removed[heavy_vertex] = true;
            } else {
                separate_connected(graph, weights, part, cost, embedding, &mut removed, work);
            }
            return Ok(Self::finish(graph, removed, work));
        }
        Ok(Self { removed: Vec::new(), components: parts })
    }

    fn finish(graph: &EmbeddedGraph, removed: Vec<bool>, work: &mut Work) -> Self {
        let components = components(graph, &removed, work);
        let mut vertices = Vec::new();
        for (v, &is_removed) in removed.iter().enumerate() {
            visit(work);
            if is_removed {
                vertices.push(v);
            }
        }
        Self { removed: vertices, components }
    }
}

fn separate_connected(
    graph: &EmbeddedGraph,
    weights: &[u64],
    part: &[usize],
    total: u128,
    embedding: Embedding,
    removed: &mut [bool],
    work: &mut Work,
) {
    let n = graph.rotations.len();
    let mut level = vec![NONE; n];
    let mut parent_dart = vec![NONE; n];
    let mut queue = Vec::with_capacity(part.len());
    let root = part[0];
    level[root] = 0;
    queue.push(root);
    let mut counts = Vec::new();
    let mut costs = Vec::new();
    let mut head = 0;
    while head < queue.len() {
        let v = queue[head];
        head += 1;
        visit(work);
        let l = level[v];
        if counts.len() <= l {
            counts.push(0usize);
            costs.push(0u128);
        }
        counts[l] += 1;
        costs[l] += u128::from(weights[v]);
        for &d in &graph.rotations[v] {
            visit(work);
            let u = graph.darts[d].target;
            if level[u] == NONE {
                level[u] = l + 1;
                parent_dart[u] = graph.darts[d].twin;
                queue.push(u);
            }
        }
    }
    let mut prefix = 0;
    let mut median = 0;
    for (l, &cost) in costs.iter().enumerate() {
        visit(work);
        prefix += cost;
        if prefix >= total / 2 + total % 2 {
            median = l;
            break;
        }
    }
    counts.push(0); // Empty upper sentinel.
    let mut a = 0;
    let mut score = usize::MAX;
    for (l, &count) in counts.iter().enumerate().take(median + 1) {
        visit(work);
        let candidate = count + 2 * (median - l);
        if candidate < score {
            score = candidate;
            a = l;
        }
    }
    let mut b = median + 1;
    score = usize::MAX;
    for (l, &count) in counts.iter().enumerate().skip(median + 1) {
        visit(work);
        let candidate = count + 2 * (l - median - 1);
        if candidate < score {
            score = candidate;
            b = l;
        }
    }
    let mut middle_cost = 0;
    for &v in part {
        visit(work);
        let l = level[v];
        if l == a || l == b {
            removed[v] = true;
        } else if a < l && l < b {
            middle_cost += u128::from(weights[v]);
        }
    }
    let limit = total / 3 * 2 + (total % 3 * 2) / 3;
    if middle_cost <= limit {
        return;
    }
    let minor = contract_prefix(graph, weights, &queue, &level, &parent_dart, a, b, embedding, work);
    let cycle = balanced_cycle(&minor, limit, work);
    for (v, &on_cycle) in cycle.iter().enumerate().take(minor.original.len()) {
        visit(work);
        let original = minor.original[v];
        if on_cycle && original != NONE {
            removed[original] = true;
        }
    }
}

struct Minor {
    graph: EmbeddedGraph,
    original: Vec<usize>,
    weights: Vec<u128>,
    parent: Vec<usize>,
    tree_edge: Vec<bool>,
}

fn unlink(d: usize, next: &mut [usize], prev: &mut [usize], starts: &mut [usize], owner: &[usize]) {
    let v = owner[d];
    if next[d] == d {
        starts[v] = NONE;
    } else {
        next[prev[d]] = next[d];
        prev[next[d]] = prev[d];
        if starts[v] == d {
            starts[v] = next[d];
        }
    }
}

#[allow(clippy::too_many_arguments)]
fn contract_prefix(
    graph: &EmbeddedGraph,
    weights: &[u64],
    queue: &[usize],
    level: &[usize],
    parent_dart: &[usize],
    a: usize,
    b: usize,
    embedding: Embedding,
    work: &mut Work,
) -> Minor {
    let Embedding { owner, mut next, mut prev } = embedding;
    let mut starts: Vec<usize> = graph.rotations.iter().map(|r| r.first().copied().unwrap_or(NONE)).collect();
    let mut keep = vec![false; graph.darts.len()];
    let mut map = vec![NONE; graph.rotations.len()];
    let mut original = vec![NONE];
    let mut costs = vec![0];
    for &v in queue {
        visit(work);
        if level[v] <= a {
            map[v] = 0;
        } else if level[v] < b {
            map[v] = original.len();
            original.push(v);
            costs.push(u128::from(weights[v]));
        }
    }
    for (d, dart) in graph.darts.iter().enumerate() {
        visit(work);
        let u = owner[d];
        let v = dart.target;
        let internal_tree = parent_dart[u] == d || parent_dart[v] == dart.twin;
        keep[d] = map[u] != NONE && map[v] != NONE && u != v
            && (map[u] != map[v] || internal_tree);
        if !keep[d] {
            unlink(d, &mut next, &mut prev, &mut starts, &owner);
        }
    }
    // Reverse BFS order contracts children before parents. Rotation splices do
    // not relabel incident darts; endpoint ownership is mapped in one final pass.
    for &v in queue.iter().rev() {
        visit(work);
        if level[v] == 0 || level[v] > a {
            continue;
        }
        let d = parent_dart[v];
        let t = graph.darts[d].twin;
        let p = graph.darts[d].target;
        let dn = next[d];
        let dp = prev[d];
        let tn = next[t];
        let tp = prev[t];
        let child_empty = dn == d;
        let parent_empty = tn == t;
        starts[p] = match (child_empty, parent_empty) {
            (true, true) => NONE,
            (true, false) => { next[tp] = tn; prev[tn] = tp; tn }
            (false, true) => { next[dp] = dn; prev[dn] = dp; dn }
            (false, false) => {
                next[dp] = tn;
                prev[tn] = dp;
                next[tp] = dn;
                prev[dn] = tp;
                tn
            }
        };
        keep[d] = false;
        keep[t] = false;
    }
    let mut darts = Vec::new();
    let mut dart_map = vec![NONE; graph.darts.len()];
    for (d, &retained) in keep.iter().enumerate() {
        visit(work);
        if retained {
            dart_map[d] = darts.len();
            darts.push(Dart { target: map[graph.darts[d].target], twin: NONE });
        }
    }
    for (d, &retained) in keep.iter().enumerate() {
        visit(work);
        if retained {
            darts[dart_map[d]].twin = dart_map[graph.darts[d].twin];
        }
    }
    let mut rotations = vec![Vec::new(); original.len()];
    for (v, rotation) in rotations.iter_mut().enumerate() {
        visit(work);
        let old = if v == 0 { queue[0] } else { original[v] };
        let first = starts[old];
        if first != NONE {
            let mut d = first;
            loop {
                visit(work);
                rotation.push(dart_map[d]);
                d = next[d];
                if d == first {
                    break;
                }
            }
        }
    }
    let mut parent = vec![NONE; original.len()];
    let mut tree_edge = vec![false; darts.len()];
    for v in 1..original.len() {
        visit(work);
        let d = dart_map[parent_dart[original[v]]];
        parent[v] = darts[d].target;
        tree_edge[d] = true;
        tree_edge[darts[d].twin] = true;
    }
    Minor { graph: EmbeddedGraph { darts, rotations }, original, weights: costs, parent, tree_edge }
}

struct Triangulation {
    darts: Vec<Dart>,
    owner: Vec<usize>,
    faces: Vec<[usize; 3]>,
    face_of: Vec<usize>,
    parent: Vec<usize>,
    tree_edge: Vec<bool>,
    weights: Vec<u128>,
    initial: usize,
}

fn triangulate(minor: &Minor, work: &mut Work) -> Triangulation {
    let graph = &minor.graph;
    let mut owner = Vec::with_capacity(3 * graph.darts.len());
    owner.resize(graph.darts.len(), NONE);
    let mut prev = vec![NONE; graph.darts.len()];
    for (v, r) in graph.rotations.iter().enumerate() {
        visit(work);
        for (i, &d) in r.iter().enumerate() {
            visit(work);
            owner[d] = v;
            prev[d] = r[(i + r.len() - 1) % r.len()];
        }
    }
    let mut seen = vec![false; graph.darts.len()];
    let mut darts = Vec::with_capacity(3 * graph.darts.len());
    darts.extend_from_slice(&graph.darts);
    let mut parent = Vec::with_capacity(minor.parent.len() + graph.darts.len());
    parent.extend_from_slice(&minor.parent);
    let mut weights = Vec::with_capacity(minor.weights.len() + graph.darts.len());
    weights.extend_from_slice(&minor.weights);
    let mut tree_edge = Vec::with_capacity(3 * graph.darts.len());
    tree_edge.extend_from_slice(&minor.tree_edge);
    let mut face_of = Vec::with_capacity(3 * graph.darts.len());
    face_of.resize(graph.darts.len(), NONE);
    work.separator_visits += (2 * graph.darts.len() + 2 * minor.parent.len()) as u128;
    let mut result = Triangulation {
        darts, owner, faces: Vec::with_capacity(graph.darts.len()), face_of,
        parent, tree_edge, weights, initial: NONE,
    };
    let mut spoke = vec![NONE; graph.darts.len()];
    let mut boundary = Vec::new();
    for start in 0..graph.darts.len() {
        visit(work);
        if seen[start] {
            continue;
        }
        boundary.clear();
        let mut d = start;
        loop {
            visit(work);
            seen[d] = true;
            boundary.push(d);
            d = prev[graph.darts[d].twin];
            if d == start {
                break;
            }
        }
        let hub = result.parent.len();
        result.weights.push(0);
        // Prefer the contracted root as hub parent. An initial cycle through
        // this hub and another spoke contains root, keeping root outside every
        // subsequent strict heavy interior.
        let mut parent_corner = 0;
        for (i, &e) in boundary.iter().enumerate() {
            visit(work);
            if result.owner[e] == 0 {
                parent_corner = i;
                break;
            }
        }
        result.parent.push(result.owner[boundary[parent_corner]]);
        for (i, &e) in boundary.iter().enumerate() {
            visit(work);
            let s = result.darts.len();
            spoke[e] = s;
            result.darts.push(Dart { target: hub, twin: s + 1 });
            result.darts.push(Dart { target: result.owner[e], twin: s });
            result.owner.push(result.owner[e]);
            result.owner.push(hub);
            result.face_of.push(NONE);
            result.face_of.push(NONE);
            result.tree_edge.push(i == parent_corner);
            result.tree_edge.push(i == parent_corner);
            if result.initial == NONE && result.owner[boundary[parent_corner]] == 0 && i != parent_corner {
                result.initial = s;
            }
        }
        for i in 0..boundary.len() {
            visit(work);
            let e = boundary[i];
            let following = boundary[(i + 1) % boundary.len()];
            let face = [e, spoke[following], spoke[e] + 1];
            let f = result.faces.len();
            for &edge in &face {
                result.face_of[edge] = f;
            }
            result.faces.push(face);
        }
    }
    result
}

// The perimeter is the tree path between the current non-tree edge's endpoints.
// Its two undirected neighbor slots avoid reversals when a path is spliced.
struct Perimeter {
    member: Vec<bool>,
    neighbors: Vec<[usize; 2]>,
    cost: u128,
}

impl Perimeter {
    fn connect(&mut self, a: usize, b: usize) {
        let i = usize::from(self.neighbors[a][0] != NONE);
        self.neighbors[a][i] = b;
        let j = usize::from(self.neighbors[b][0] != NONE);
        self.neighbors[b][j] = a;
    }
    fn disconnect(&mut self, a: usize, b: usize) {
        let i = usize::from(self.neighbors[a][0] != b);
        self.neighbors[a][i] = NONE;
        let j = usize::from(self.neighbors[b][0] != a);
        self.neighbors[b][j] = NONE;
    }
    fn remove_arc(&mut self, mut v: usize, stop: usize, weights: &[u128], work: &mut Work) {
        while v != stop {
            visit(work);
            let [a, b] = self.neighbors[v];
            let next = if a == NONE { b } else { a };
            self.disconnect(v, next);
            self.member[v] = false;
            self.cost -= weights[v];
            v = next;
        }
    }
}

struct Scan {
    stack: Vec<(usize, usize)>,
    cost: u128,
    epoch: usize,
}
impl Scan {
    fn step(
        &mut self,
        t: &Triangulation,
        perimeter: &Perimeter,
        seen: &mut [usize],
        work: &mut Work,
    ) {
        if let Some((f, parent)) = self.stack.pop() {
            visit(work);
            for &d in &t.faces[f] {
                visit(work);
                let v = t.owner[d];
                if !perimeter.member[v] && seen[v] != self.epoch {
                    seen[v] = self.epoch;
                    self.cost += t.weights[v];
                }
                if !t.tree_edge[d] {
                    let other = t.face_of[t.darts[d].twin];
                    if other != parent {
                        self.stack.push((other, f));
                    }
                }
            }
        }
    }
}

fn balanced_cycle(minor: &Minor, limit: u128, work: &mut Work) -> Vec<bool> {
    let t = triangulate(minor, work);
    let n = t.parent.len();
    let mut perimeter = Perimeter { member: vec![false; n], neighbors: vec![[NONE; 2]; n], cost: 0 };
    let mut edge = t.initial;
    let mut u = t.owner[edge];
    let mut v = t.darts[edge].target;
    // The chosen edge has one hub endpoint whose parent is root. Construct its
    // fundamental cycle without an LCA oracle or repeated parent-path scans.
    let hub = if u >= minor.original.len() { u } else { v };
    let original = if hub == u { v } else { u };
    perimeter.member[hub] = true;
    perimeter.member[0] = true;
    perimeter.connect(hub, 0);
    let mut child = original;
    perimeter.member[child] = true;
    perimeter.cost += t.weights[child];
    while child != 0 {
        visit(work);
        let p = t.parent[child];
        perimeter.connect(child, p);
        if !perimeter.member[p] {
            perimeter.member[p] = true;
            perimeter.cost += t.weights[p];
        }
        child = p;
    }
    let f0 = t.face_of[edge];
    let f1 = t.face_of[t.darts[edge].twin];
    let mut seen = vec![0usize; n];
    let mut left = Scan { stack: vec![(f0, f1)], cost: 0, epoch: 1 };
    let mut right = Scan { stack: vec![(f1, f0)], cost: 0, epoch: 2 };
    while !left.stack.is_empty() {
        left.step(&t, &perimeter, &mut seen, work);
    }
    while !right.stack.is_empty() {
        right.step(&t, &perimeter, &mut seen, work);
    }
    let mut inside_face = if left.cost >= right.cost { f0 } else { f1 };
    let mut inside_cost = left.cost.max(right.cost);
    let total: u128 = t.weights.iter().copied().sum();
    work.separator_visits += n as u128;
    let mut epoch = 2usize;
    let mut path = Vec::new();
    // Reuse the two traversal stacks. Degree at most three bounds the work of
    // each step; alternating scans charge at most twice the discarded faces.
    while inside_cost > limit {
        visit(work);
        let face = t.faces[inside_face];
        let mut branches = [NONE; 2];
        let mut branch_count = 0;
        let mut y = NONE;
        for &d in &face {
            visit(work);
            let w = t.owner[d];
            if w != u && w != v {
                y = w;
            }
            if d != edge && t.darts[d].twin != edge && !t.tree_edge[d] {
                branches[branch_count] = d;
                branch_count += 1;
            }
        }
        // A cotree leaf bounds an empty strict interior and cannot be heavy.
        assert!(branch_count != 0, "heavy cotree leaf");
        path.clear();
        let mut z = y;
        let mut path_cost = 0;
        while !perimeter.member[z] {
            visit(work);
            path.push(z);
            path_cost += t.weights[z];
            perimeter.member[z] = true;
            z = t.parent[z];
        }
        let mut chosen = branches[0];
        let mut next_cost = inside_cost - path_cost;
        if branch_count == 2 {
            epoch += 2;
            left.stack.clear();
            right.stack.clear();
            left.cost = 0;
            right.cost = 0;
            left.epoch = epoch - 1;
            right.epoch = epoch;
            left.stack.push((t.face_of[t.darts[branches[0]].twin], inside_face));
            right.stack.push((t.face_of[t.darts[branches[1]].twin], inside_face));
            // Strict interiors are disjoint. Their common boundary is already
            // excluded, so interleaved traversals can share one stamp arena.
            while !left.stack.is_empty() && !right.stack.is_empty() {
                left.step(&t, &perimeter, &mut seen, work);
                right.step(&t, &perimeter, &mut seen, work);
            }
            let (cost0, cost1) = if left.stack.is_empty() {
                (left.cost, next_cost - left.cost)
            } else {
                (next_cost - right.cost, right.cost)
            };
            if cost1 > cost0 {
                chosen = branches[1];
                next_cost = cost1;
            } else {
                next_cost = cost0;
            }
        }
        let a = t.owner[chosen];
        let b = t.darts[chosen].target;
        let kept = if a == u || b == u { u } else { v };
        let dropped = if kept == u { v } else { u };
        perimeter.remove_arc(dropped, z, &t.weights, work);
        let mut p = z;
        for &w in path.iter().rev() {
            visit(work);
            perimeter.connect(p, w);
            p = w;
        }
        perimeter.cost += path_cost;
        edge = chosen;
        u = a;
        v = b;
        inside_face = t.face_of[t.darts[edge].twin];
        inside_cost = next_cost;
        // Before a heavy interior becomes light, the split retains at least
        // half the old interior after charging its shared path to the boundary.
        // A one-branch move can send only one old boundary vertex outside;
        // its cost is at most W/3, so the exterior cannot become heavy.
        debug_assert!(inside_cost > limit || total - inside_cost - perimeter.cost <= limit);
    }
    perimeter.member
}

#[cfg(test)]
mod tests {
    use super::*;

    // Ordered neighbor lists make the embedding explicit; no angle sorting.
    fn graph(neighbors: Vec<Vec<usize>>) -> EmbeddedGraph {
        let mut darts = Vec::new();
        let mut rotations = Vec::new();
        for row in &neighbors {
            let mut rotation = Vec::new();
            for &target in row {
                rotation.push(darts.len());
                darts.push(Dart { target, twin: NONE });
            }
            rotations.push(rotation);
        }
        for v in 0..neighbors.len() {
            for &d in &rotations[v] {
                if darts[d].twin == NONE {
                    let target = darts[d].target;
                    let t = rotations[target].iter().copied()
                        .find(|&t| darts[t].target == v && darts[t].twin == NONE && t != d).unwrap();
                    darts[d].twin = t;
                    darts[t].twin = d;
                }
            }
        }
        EmbeddedGraph { darts, rotations }
    }

    fn check(graph: &EmbeddedGraph, weights: &[u64]) -> Separator {
        let mut work = Work::default();
        let result = Separator::build(graph, weights, &mut work).unwrap();
        let total: u128 = weights.iter().map(|&w| u128::from(w)).sum();
        let limit = total / 3 * 2 + total % 3 * 2 / 3;
        let mut label = vec![NONE; weights.len()];
        for &v in &result.removed {
            assert_eq!(label[v], NONE);
            label[v] = usize::MAX - 1;
        }
        for (c, component) in result.components.iter().enumerate() {
            let cost: u128 = component.iter().map(|&v| u128::from(weights[v])).sum();
            assert!(cost <= limit);
            for &v in component {
                assert_eq!(label[v], NONE);
                label[v] = c;
            }
        }
        assert!(label.iter().all(|&c| c != NONE));
        for (v, rotation) in graph.rotations.iter().enumerate() {
            for &d in rotation {
                let u = graph.darts[d].target;
                assert!(label[u] == label[v] || label[u] == usize::MAX - 1 || label[v] == usize::MAX - 1);
            }
        }
        assert!(result.removed.len() * result.removed.len() <= 8 * weights.len());
        assert_eq!(result, Separator::build(graph, weights, &mut Work::default()).unwrap());
        result
    }

    #[test]
    fn empty_single_and_zero_weight() {
        check(&graph(vec![]), &[]);
        assert_eq!(check(&graph(vec![vec![]]), &[7]).removed, vec![0]);
        assert!(check(&graph(vec![vec![1], vec![0]]), &[0, 0]).removed.is_empty());
    }

    #[test]
    fn long_paths_and_stars() {
        let n = 1001;
        let mut path = vec![Vec::new(); n];
        for i in 1..n {
            path[i - 1].push(i);
            path[i].push(i - 1);
        }
        check(&graph(path), &vec![1; n]);
        let mut star = vec![Vec::new(); n];
        for i in 1..n {
            star[0].push(i);
            star[i].push(0);
        }
        assert!(check(&graph(star), &vec![1; n]).removed.contains(&0));
    }

    #[test]
    fn nested_cycle_search_on_wheels() {
        for rim in [7, 64, 251] {
            let mut neighbors = vec![Vec::new(); rim + 1];
            neighbors[0] = (1..=rim).collect();
            for (v, row) in neighbors.iter_mut().enumerate().skip(1) {
                let previous = if v == 1 { rim } else { v - 1 };
                let next = if v == rim { 1 } else { v + 1 };
                *row = vec![0, previous, next];
            }
            let g = graph(neighbors);
            check(&g, &vec![1; rim + 1]);
            let weights: Vec<u64> = (0..=rim).map(|v| if v % 3 == 0 { 4 } else { 1 }).collect();
            check(&g, &weights);
        }
    }

    fn grid(rows: usize, columns: usize) -> EmbeddedGraph {
        let mut neighbors = vec![Vec::new(); rows * columns];
        for y in 0..rows {
            for x in 0..columns {
                let v = y * columns + x;
                if x + 1 < columns { neighbors[v].push(v + 1); }
                if y + 1 < rows { neighbors[v].push(v + columns); }
                if x > 0 { neighbors[v].push(v - 1); }
                if y > 0 { neighbors[v].push(v - columns); }
            }
        }
        graph(neighbors)
    }

    #[test]
    fn grids_and_nonuniform_weights() {
        for (r, c) in [(2, 91), (19, 23), (31, 31)] {
            let g = grid(r, c);
            check(&g, &vec![1; r * c]);
            let weights: Vec<u64> = (0..r * c).map(|i| if i % 7 == 0 { 11 } else { 0 }).collect();
            check(&g, &weights);
        }
    }

    #[test]
    fn repeated_face_vertices_and_disconnected_weights() {
        // Two triangles joined by a bridge: its outer walk repeats vertices.
        let g = graph(vec![vec![1, 2], vec![2, 0], vec![0, 1, 3], vec![2, 4, 5], vec![5, 3], vec![3, 4], vec![]]);
        check(&g, &[3, 2, 4, 4, 2, 3, 1]);
        let disconnected = graph(vec![vec![1], vec![0], vec![3], vec![2], vec![]]);
        assert!(check(&disconnected, &[2, 2, 2, 2, 1]).removed.is_empty());
        check(&disconnected, &[9, 1, 0, 0, 0]);
        // Parallel contacts and a loop do not change vertex separation.
        check(&graph(vec![vec![0, 0, 1, 1], vec![0, 0]]), &[1, 1]);
    }

    #[test]
    fn invalid_twin_rotation_and_planarity() {
        let mut g = graph(vec![vec![1], vec![0]]);
        g.darts[0].twin = 0;
        assert_eq!(Separator::build(&g, &[1, 1], &mut Work::default()), Err(SeparatorError::InvalidTwin));
        let mut g = graph(vec![vec![1], vec![0]]);
        g.rotations[0].push(0);
        assert_eq!(Separator::build(&g, &[1, 1], &mut Work::default()), Err(SeparatorError::InvalidRotation));
        let k33 = graph(vec![vec![3, 4, 5], vec![3, 4, 5], vec![3, 4, 5], vec![0, 1, 2], vec![0, 1, 2], vec![0, 1, 2]]);
        assert_eq!(Separator::build(&k33, &[1; 6], &mut Work::default()), Err(SeparatorError::NonPlanarRotation));
        assert_eq!(Separator::build(&graph(vec![vec![]]), &[], &mut Work::default()), Err(SeparatorError::WeightCount));
    }
}
