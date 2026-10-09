# Chazelle triangulation: paper map for a Rust implementation

## Scope and source

**Target:** Bernard Chazelle, *Triangulating a Simple Polygon in Linear Time*,
Discrete & Computational Geometry **6**, 485–524 (1991).
[Primary paper](https://www.cs.princeton.edu/~chazelle/pubs/polygon-triang.pdf).

The target is deterministic worst-case linear-time triangulation of an arbitrary
simple polygon, not just a convex polygon and not Seidel's randomized algorithm.
The Rust implementation now includes the complete construction: exact input and
boundary geometry, saved-chain fusion/restoration and separator queries, local
symbolic refinement, closed-map conversion, and original-vertex triangulation.
This document separates paper definitions and bounds from derived implementation
choices. It is a source map, not a machine-checked correctness or runtime proof.

Citations use printed journal pages. In the linked 40-page PDF, PDF page = journal
page − 484. The PDF is scanned: OCR was used for navigation, with the definitions,
lemma bounds, and hierarchy formulas checked against the page images.

The paper's main construction produces a **horizontal visibility map**. Conversion
to a triangulation is a separate linear-time reduction cited to earlier papers
(§1, pp.486–487; Theorem 4.3, p.521). That reduction is a required implementation
dependency, not something to replace with ear clipping.

The executable geometry contracts are specified in
[GEOMETRY_BOUNDARY_SPEC.md](GEOMETRY_BOUNDARY_SPEC.md): exact affine normalization,
curve-local boundary occurrences, chord routes, arc weights, and seam/padding.

## 1. Reading order and deliverables

| Paper location | Construction / result | What it supplies to implementation |
|---|---|---|
| §1, pp.485–488 | Bottom-up approximation, top-down refinement | Overall algorithm; why full-map merging at every grade would cost O(n log n) |
| §2.1, pp.489–493 | Spherical plane, double boundary, visibility map/tree; Lemma 2.1 | Geometric/topological identity and visibility separation |
| §2.2, pp.493–495 | Augmentation, submaps, canonical order, weights; Lemma 2.2 | Boundary operations and region/global order agreement |
| §2.3, pp.495–497 | Conformality, tree decomposition, granularity; Lemma 2.3 | Bounded degree, succinct maps, logarithmic-depth searches |
| §2.4, pp.497–499 | Normal form and double identification | Shared input representation and navigation contracts |
| §2.5, pp.499–500 | Shielding; Lemma 2.4 | Sound branch rejection during conformality restoration |
| §3, pp.500–502 | Merge preconditions and abstract oracles | Interfaces separating merge logic from oracle implementation |
| §3.1, pp.502–508 | Fusion; Lemma 3.1 | Find changed visibility at retained chord endpoints |
| §3.2, pp.508–512 | Witness search, existence, restoration; Lemmas 3.2–3.4 | Add chords until every region has at most four exits |
| §3.3, p.512 | Maintain granularity; Lemma 3.5 | Complete merge by safe chord removal and normal-form reconstruction |
| §3.4, pp.512–516 | Separator-based ray shooting; Lemma 3.6 | Sublinear queries on preprocessed coarse maps |
| §4.1, pp.516–518 | Chains/grades, canonical submaps; Lemma 4.1 | Up-phase and concrete arc-cutter/ray-shooter realization |
| §4.2, pp.518–521 | Region refinement; Lemma 4.2, Theorem 4.3 | Down-phase and final linear-time visibility map |
| §5, pp.521–523 | Applications and open problems | Context only; simplicity checking and other applications are outside this implementation map |

The vocabulary for the hierarchy is **chains in grades** (§4), not an unspecified
“gradation.” Read §2 before designing the Rust topology: coordinate-only polygon
adjacency is insufficient.

## 2. Geometry that the implementation must preserve

### Input assumptions and the spherical plane

Section 2 initially assumes distinct y-coordinates for distinct input vertices
(p.488). It delegates degeneracy handling to symbolic perturbation, references
[10] and [31]. The main visibility construction takes a simple **nonclosed**
polygonal curve C. Section 2.4 permits puncturing a small hole for closed input
(p.497). The geometry/boundary specification supplies an exact-rational affine
normalization and an explicit seam construction as alternatives to infinitesimals.

The ambient space is the paper's spherical plane, not the Euclidean plane with a
single generic outside sentinel. Its identifications are (§2, p.489):

- (−∞, y) = (+∞, y);
- (x, −∞) = (−x, −∞);
- (x, +∞) = (−x, +∞).

A horizontal chord can wrap through horizontal infinity and still hit the curve.
Orientation is fixed using reference point (0, +∞). **Proposal:** encode finite
versus wrapping chord routes explicitly; do not use IEEE infinities as a substitute
for this topology.

### Double boundary, companions, and null chords

The curve is conceptually thickened to a thin polygon with double boundary ∂C.
No actual numerical thickening is performed (§2.1, pp.490–491).

- An ordinary interior vertex has two companion boundary occurrences.
- An interior y-extremum has four boundary occurrences: two adjacent duplicates
  on each side, with companion pairing within each side (p.490). The inside pair
  is joined by a null-length chord.
- A curve endpoint has two adjacent companions/duplicates, on opposite sides.
- Every intrinsic vertex of ∂C has one incident visibility-map chord. Every
  boundary point has an assigned horizontal direction.
- An inserted chord endpoint may lie inside an input edge; it is not an intrinsic
  vertex of ∂C.

Equal coordinates do not imply equal boundary identity. A null chord is still a
separator and can bound an empty region. **Proposal:** keep input vertex identity,
boundary side/occurrence, duplicate slot, and inserted endpoint identity distinct.

Two boundary points see each other when the relevant open horizontal route lies
outside the thin curve. Lemma 2.1 (p.492) says removing a mutually visible pair
separates the boundary into pieces that no chord connects. This is the separation
fact used in the visibility-tree proof, local shooting, and fusion's skip rules.

### Submaps and boundary operations

The full map may be augmented with chords at previously unoccupied boundary
points. Deleting chords yields a submap. A nonempty region boundary alternates
exit chords and arcs of **∂C**, not arcs of the underlying single curve C (§2.2).

Deletion also removes chord endpoints that are not intrinsic ∂C vertices and
coalesces the boundary there. Leaving orphan edge subdivisions breaks the paper's
weight and size arguments. Null chords obey the same combinatorial rules.

Lemma 2.2 (p.494) aligns a region's counterclockwise arc order with clockwise order
along ∂C. Canonical endpoint enumeration includes only retained exit endpoints;
it does not scan every original vertex. Canonical region traversal may repeat a
region.

## 3. Four distinct structural invariants

| Invariant | Exact paper meaning | Dependency |
|---|---|---|
| Dual tree | One node per region, including empty regions; one edge per retained chord, including null chords | Chord separation; deletion contracts tree edges |
| Conformality | Every dual node has degree at most 4 | Constantly many arcs/exits per region |
| γ-semigranularity | Every region's weight is at most γ | Bounds local boundary work |
| γ-granularity | Semigranularity, plus every contraction of an edge incident to at least one degree-<3 node produces weight strictly greater than γ | Prevents excessive retained regions |

An empty region has weight 0. A nonempty region's weight is the maximum number of
**nonnull-length edges in any one arc**, not the sum over arcs (§2.2, p.494).
Opposite-side subdivisions do not count as subdivisions of that arc. Removing a
chord cleans up nonintrinsic endpoints, so a contracted weight is not generally
the sum of the old weights.

Lemma 2.3 (p.496): a γ-granular conformal submap for an n-vertex curve has
O(n/γ + 1) regions, each bounded by O(γ) edges. Both conformality and full
granularity are needed; semigranularity alone does not give the region-count bound.

The **binary tree decomposition** is separate from the dual tree. Internal nodes
name chords; leaves name regions. A centroid-based edge split leaves at most
three-quarters of the old edges in either child. Its depth is logarithmic in region
count r, and the paper's chosen construction costs O(r log r + 1) (§2.3,
pp.495–496). There is no requirement for a dynamic balanced-tree implementation.

## 4. Normal form: storage contract before merge code

Section 2.4, pp.497–499, requires one ordered **read-only input-edge table**, never
modified or copied. Double-boundary geometry is implicit, not a duplicate edge
array. Each submap has:

1. Its dual-tree adjacency structure.
2. Each chord with references to its two, three, or four adjacent arc structures;
   each arc points back to its incident region.
3. Arc structures in canonical double-boundary order, plus input-chain endpoint
   markers and pointers to arcs passing through those endpoints.
4. A binary tree decomposition whenever the map is conformal.

A nonnull arc is represented by first/last input-edge pointers and side flags,
not a copied list of all its edges. Null arcs can be explicit. Arcs can
**double-back** around a chain endpoint, so an arc is not always a monotone interval
on one side of the input.

**Double identification** retrieves all arcs through a given point on a named
input edge. It uses binary searches on the canonical sequences and within an edge,
takes logarithmic time in arc count, and returns at most six arcs. Normal form
deliberately omits a global correspondence between opposite-side features; it is
not a full DCEL with constant-time arbitrary crossing.

This omission matters: storing each long boundary in each grade can introduce
Θ(n log n) redundancy even when the distinct features total O(n) (p.498).

## 5. Merge: the central constructive dependency

### Preconditions and oracles

Lemma 3.5 (p.512) merges C₁ and C₂ sharing one input vertex, whose union is a
connected vertex-to-vertex piece of the original simple open curve. Inputs are
normal-form γ₁- and γ₂-granular conformal maps with γ₁ ≤ γ₂. Requested output
granularity γ must satisfy γ ≥ γ₂. This is not a general planar-overlay operation.

The two assumed services (§3, p.501) operate on an input region arc and a specified
subarc with endpoint edge names and double-boundary side flags:

| Service | Required answer | Cost / guarantee |
|---|---|---|
| Ray shooter | First hit of a left/right horizontal ray against that subarc, with containing input-edge name, or no hit | O(f(γᵢ)); not visibility against the entire curve |
| Arc cutter | At most g(γᵢ) non-double-backing subarcs, with already-available normal-form h(γᵢ)-granular conformal maps of their underlying vertex-to-vertex chains | O(g(γᵢ)); at most two exceptional single-edge endpoint pieces |

The cutter returns saved structures, not permission to compute them by scanning a
chain. The functions f, g, h are nondecreasing; h is an output-granularity bound,
not a third oracle. A geometric hit must still pass side/orientation checks.

### Stage A: fusion — §3.1, Lemma 3.1

Perform one clockwise traversal of retained endpoints of S₁ against S₂, then the
symmetric pass. Startup handles the duplicated common vertex and locally entered
region. Local shooting checks the constantly many arcs of a known region.

The traversal maintains: all earlier endpoint visibility answers are known; the
current point sees C₂ through the current S₂ region. Its ordered events are:

1. A candidate endpoint is in that region and sees C₂: record it and advance.
2. Otherwise, an exit endpoint of the region sees a later point of the current
   S₁ arc: take the **last clockwise** candidate and cross that exit.
3. Otherwise, exhaust the remaining arc sequence and finish.

The reverse shot in event 2 is essential: hitting one target arc does not prove
that another C₁ arc does not obstruct visibility. Strict clockwise progress and
the dual-tree argument justify skipping intervening endpoints (pp.504–507).

Retain newly found cross-curve chords, surviving old chords, **all input null
chords**, and common-vertex companion chords. Build canonical arc order and
adjacency. Fusion need not be conformal, but each region has constantly many arcs,
and every new arc stays within an original input arc. Preserve that provenance
for subsequent oracle calls. Do not build a conformal decomposition prematurely.

### Stage B: restore conformality — §3.2, Lemmas 3.2–3.4

For each region with more than four arcs, search nonconsecutive arc pairs for a
visibility chord and insert it. Lemma 3.3 guarantees a suitable pair with an
original-vertex witness; the search may return a point that is not an original
vertex. Ordered pair search avoids assuming which arc contains the witness.

Lemma 3.2 cuts an arc into saved smaller submaps, descends their binary
decompositions, then searches a leaf's O(h(γ₂)) boundary. Lemma 2.4's **shielding**
argument certifies the rejected child. It is a topological decision from boundary
order and first/last chord intersections, not a coordinate heuristic. Those
intersections are first/last along the chord, not along the crossing curve.

The existence proof uses the conceptual augmented full visibility tree. It does
not instruct the implementation to build that full tree during a merge.

### Stage C: restore granularity — §3.3, Lemma 3.5

After restoration, the result is γ₂-semigranular. For target γ ≥ γ₂, process each
exit chord once: if it has a degree-<3 incident node and its removal would produce
actual weight ≤ γ, remove it, clean up nonintrinsic endpoints, and contract the
dual edge. Such a contraction preserves degree ≤4. The paper states that removals
cannot make a previously nonremovable chord removable and permits arbitrary
one-pass order.

**Implementation distinction:** `submap::Submap::coarsen` reconsiders the surviving
neighbors of every contraction. A chord initially joining two degree-≥3 regions
can become eligible after null-leaf removal in a supported augmented map.
The queue preserves the paper's exact degree/weight predicate. A contraction
joins a degree-≤2 region to a degree-≤4 region, leaving at most four exits, so
neighbor reconsideration still takes O(number of retained chords) work.

Reconstruct complete normal form, including its decomposition. No slower fallback
is part of any of these stages.

## 6. Realizing the oracles

### Separator-based ray shooting — §3.4, Lemma 3.6

Temporarily collapse the double boundary to a planar subdivision S*: remove
zero-length geometry and place chord endpoints on both sides. Nonempty regions
become faces; empty regions have no face. A face may have many collinear
subdivisions even when the corresponding region has O(γ) edges. Scan **region
arcs**, not all those face subdivisions.

Construct the planar face-dual graph G with μ = O(m/γ + 1) nodes. This is not the
submap's dual tree. Adjacencies arise both across chords and where a chord endpoint
on one side abuts an arc on the other, found using double identification/order
(§3.4, pp.513–514).

Use the linear-time Lipton–Tarjan separator construction recursively to form a
union of separators and remaining groups, both of size O(μ^(2/3)). A ray query
scans separator regions, identifies the remaining group via the nearest hit and
local orientation, then scans that group. If no separator region is hit, a
preprocessed vertical line to the right of the input locates the group. Account
for wrapping routes and logarithmic double identification (pp.514–515).

Lemma 3.6 (p.516): preprocessing costs O(m log(m)/γ + 1); each ray query costs
O(γ^(1/3) m^(2/3)). The one-face case is handled by a direct scan. Generic planar
point location is not the oracle used by this paper.

### Saved smaller grades close the apparent dependency cycle — §4.1

Pad the open curve to n = 2^p + 1 vertices. A grade-λ chain has 2^λ edges, starts
at an edge index divisible by 2^λ, and there are 2^(p−λ) such chains (§4, p.516).
Set **β = 1/5**. A canonical submap of an m-edge chain has granularity
γ(m) = 2^⌈β⌈log₂ m⌉⌉, is conformal, and is in normal form. Grade-λ granularity
is 2^⌈βλ⌉.

Process grades bottom-up, saving each canonical map and its ray-shooting
preprocessing. Constant early grades are handled directly. Lemma 4.1 (p.517)
builds a canonical map for an arbitrary interval with 2^(λ−1) < m ≤ 2^λ by
splitting into at most two saved chains per smaller grade, increasing their
granularity as needed, and merging in a balanced tree.

For a merge's arc or subarc, decompose its underlying boundary into O(λ) saved
chains of grades at most ⌈βλ⌉, plus at most two single-edge pieces. This supplies
both the ray shooter and the cutter. For sufficiently large λ, ⌈βλ⌉ < λ:
the required maps have already been constructed. A merge therefore never needs
the same map that it is currently computing.

## 7. Down-phase: not recursive retriangulation of every face

Section 4.2 starts with the coarsest canonical map of the whole curve and the
saved chain maps/oracles. For a region R:

1. Split its constantly many arcs into single edges and original vertex-to-vertex
   pieces. Build canonical maps for those pieces using Lemma 4.1.
2. Merge them with the region's exit chords as temporary **input edges**, producing
   a smaller-granularity map of R's boundary minus a vertex (an open curve).
   Symbolically tilt the temporary exits before merging (p.519); they must not
   be removable during those merges.
3. Reinterpret those input edges as chords, restoring conformality where needed.
4. Keep only chords with both endpoints on R's side-aware boundary arcs.
5. Combine the refinements, then enforce full granularity by chord removal.

The scale drops from roughly 2^(βλ) to 2^(β²λ). Iterate refinement; once local
boundary sizes are bounded, compute the remaining chords directly. Lemma 4.2
(p.518) proves refinement to the full map in time at most (c − 1/λ)2^l for a
chain in grade l ≥ λ, for sufficiently large fixed c. Theorem 4.3 (p.521) combines
both phases with the visibility-to-triangulation reduction.

## 8. Complexity ledger

Here N = n₁ + n₂ and M = n₁/γ₁ + n₂/γ₂ + 1 are shorthand for this map, not new
paper parameters. In the merge bounds the paper assumes γᵢ = O(N).

| Result | Bound | Source |
|---|---|---|
| Fusion | O(M(f(γ₂) + log N)) | Lemma 3.1, p.505 |
| Witness search | O(f(γ₂)g(γ₂)(h(γ₂) + log γ₂)) | Lemma 3.2, p.508 |
| Restore conformality | O(M f(γ₂)g(γ₂)(h(γ₂) + log γ₂)) | Lemma 3.4, p.512 |
| Complete merge | O(M f(γ₂)g(γ₂)(h(γ₂) + log N)) | Lemma 3.5, p.512 |
| Ray preprocessing / query | O(m log(m)/γ + 1) / O(γ^(1/3)m^(2/3)) | Lemma 3.6, p.516 |
| Arbitrary interval canonical map | O(λ² log(λ) 2^(λ(1 − β/3 + 4β²/3))) | Lemma 4.1, p.517 |
| Whole grade construction and preprocessing | O(n λ² log(λ) 2^(βλ(4β/3 − 1/3)) + n λ 2^(−βλ)) | §4.1, p.518 |
| All up-phase grades | O(n), using a grade bound O(n 2^(−λ/76)) for β = 1/5 | §4.1, p.518 |
| Down-phase | O(n), with refinement overhead proportional to 2^l λ² log(λ) 2^(β²λ(4β/3 − 1/3)) | Lemma 4.2 proof, p.520 |
| Full visibility map, then triangulation | O(n) | Theorem 4.3, p.521 |

For β = 1/5, the grade exponent is −λ/75 before absorbing polynomial factors;
the refinement exponent is −λ/375. Summability and the refinement induction,
not a timing graph, are the reason the total is linear. Constant early grades
avoid interpreting logarithmic formulas at λ = 0.

These are the paper's geometric-operation bounds. A Rust implementation must
separately account for arithmetic bit costs, allocation, and storage; exact
big-integer/rational work is not automatically unit-cost.

## 9. Rust component contracts and implementation status

Keep compact indexed storage, one shared input, and reusable buffers over copied
geometry or general-purpose persistent trees. The table describes the implemented
responsibilities; the API and publication contracts follow it.

| Component | State and operations | Invariant / acceptance evidence |
|---|---|---|
| `geometry` | Predicates, exact hit comparisons, strict affine y-order, chord routes | Side-aware nearest hits; exact-rational normalization without numerical epsilons |
| `boundary` | Input edge IDs, boundary occurrences, companions, intrinsic vs inserted endpoints, clipped arcs | Extrema/endpoints retain multiplicity; double-backing and null arcs preserved |
| `submap` | Map-local arc/chord/region IDs, dual adjacency, canonical arc table, endpoint markers | Degree, actual weights, endpoint cleanup, canonical order, double identification |
| `decomposition` | Internal chord / leaf region binary tree | Three-quarters split, logarithmic depth; rebuilt at the stated cost |
| `cap`, `fusion`, `witness`, `merge` | Separate output map; role-aware cap flags, two fusion passes, one-child shielding searches, restoration | Input maps remain immutable; shared-level events select the outgoing germ's region; restoration decreases excess degree |
| `separator` | Planar face-dual graph, separators, groups, vertical-line lookup | Actual linear-time planar separator; distinct from the submap tree |
| `oracle`, `arcs`, `program_queries` | Owning saved separator queries; clipped Root and displaced Programme adapters | First raw blocker with tied incidences; descriptor-aware thresholds; no hidden long-arc scan or saved-oracle rebuild |
| `hierarchy` | Chain grade/index catalog, saved canonical maps and query structures | Queries use strictly smaller processed grades; no per-grade input copies |
| `view`, `program`, `ribbon`, `collapse`, `graft`, `triangulation` | Lazy region boundaries, symbolic temporary exits, limiting-cut repair, ordered graft and scale controller | Authoritative exits, side/slot provenance, every star transit cut, actual original arc bounds, linear current-map publication |
| `closure`, `reduction` | Closed-polygon seam reversal and visibility-map conversion | Original-vertex triangle output with no artificial seam/padding vertices |
| `work` | Counters for predicate calls, scanned arc edges, oracle calls, merge events, decomposition and separator work | Cost attributable to each lemma/grade; timing reported separately |

**Decision:** use typed IDs into map-owned arenas rather than cyclic Rust references.
Keep the immutable input and saved oracle maps alive while building separate
outputs; this is not a requirement for a general persistent-data-structure library.
Double identification can return a fixed-capacity collection of six IDs without
allocating on every lookup. Choose reclamation and buffer reuse after lifetimes
are explicit; do not clone full maps merely to avoid borrow conflicts.

**Public API:** `triangulate(&[Point], &mut Work)` returns
`Result<Vec<[usize; 3]>, TriangulationError>`. Coordinates are exact rationals;
`Point::integer(x, y)` is the integer convenience constructor. The implicit closed
boundary must be a simple polygon with pairwise distinct vertices and no repeated
closing vertex. Simplicity and global distinctness are caller preconditions, not
hash-validated. Either winding and consecutive collinear boundary vertices are
supported. Output uses only caller vertex IDs and nondegenerate CCW triangles.

```rust
use chazelle_triangulation::{geometry::Point, triangulate, work::Work};

fn main() -> Result<(), chazelle_triangulation::TriangulationError> {
    let polygon = [Point::integer(0, 0), Point::integer(3, 0), Point::integer(0, 2)];
    let mut work = Work::default();
    let triangles = triangulate(&polygon, &mut work)?;
    println!("{triangles:?}");
    Ok(())
}
```

`OriginalMerge` supplies real saved-chain construction. `base::full_visibility`
has a hard input-independent bound of 16 edges; it is never an arbitrary-input
fallback. The final `completion` stage enumerates only conformal regions whose
actual original arc weights are at most 16. It restores every intrinsic chord:
granularity one alone is not a full-visibility certificate.

Published normal form compacts outer arenas and each surviving region's nested
arc/exit vectors. Its IDs expire at republication. Coarse saved maps must not
retain finer-map tombstone storage or vector capacity.

Saved normal form includes the balanced query decomposition. Current down-phase
and final maps use `publish_visibility`: canonical order follows physical endpoint
links in linear time, and no unused O(n log n) decomposition is built. Ordered
grafting likewise consumes old-arc endpoint streams without a global sort.

## 10. Construction sequence and verification

1. **Geometry:** normalize and seam/pad once; derive chain-local occurrences
   lazily from the shared input.
2. **Saved maps:** bounded leaves, faithful fusion, cyclic-order witness descent,
   conformality restoration, actual-weight contraction, compact publication,
   balanced decomposition and planar-separator preprocessing.
3. **Up-phase:** build aligned grades; arbitrary intervals use strictly earlier
   grades and balanced merges, with no input-table copies.
4. **Down-phase:** move out the root map, compile constant-description local
   ribbon programmes, query existing smaller saved chains, collapse and repair
   limiting cuts, graft, restore, and contract at the checked original scale.
5. **Completion/output:** finish bounded original regions, restore the closed
   boundary, extract original cap-generator cells, and triangulate mountains.

Independent exhaustive geometry is confined to bounded leaves and diagnostics.
Behavioral checks compare first blockers and occurrence identities, then verify
original-ID output, exact area, CCW orientation, every boundary segment once and
internal edges twice. Concave chains, collinearity, extrema, full returns, null
regions, both cap runs, shared-level fusion events, helper-generated remote cuts
and degree-changing contractions have dedicated regressions.

The ribbon simplicity diagnostic rejects only strictly disjoint closed chart
bounds. Finite/alias bounds and equations use raw affine preimages under the
common injective compactification; mixed/projective pairs retain exact quadratic
crossing and tangency checks. Interior critical points are detected by endpoint
derivative signs; their values use the exact `(4*a*c - b*b)/(4*a)` sign identity,
without constructing nested symbolic ratios. Touching bounds and chart-seam
incidences remain audited.
Its homogeneous line coefficients retain nonzero delta-Y scales instead of
constructing symbolic slopes; intersection tests clear those scales exactly.
Pairs translate the level coordinate by an exact rational origin before forming
quadratic coefficients, cancelling common base levels without approximation.

The down-phase uses the derived bound
`gamma_next = 2^ceil(ceil(log2(gamma))/5) + 2`: a final original arc inherits one
temporary support arc and at most one trimmed original edge at each endpoint.
All star transit cuts and remote equal-base blockers must survive or receive
independent first-blocker repair. For gamma > 16 this scale strictly decreases.
The +2 collar allowance is an implementation derivation, not a number printed in
Chazelle's paper. Section 10 of the geometry specification records its invariant.

`Work` accumulates instrumented predicates, arc-edge visits, retained-record
visits, oracle calls, fusion events, decomposition visits and separator visits.
These are algorithmic ledgers, not an instruction count, a coefficient-size
bound, or a timing-based proof of linearity. Exact big-integer and symbolic
arithmetic costs remain separate from the paper's geometric-operation model.

## 11. Dependency resolution

The primary-paper construction and its external dependencies are mapped below.
Derived degeneracy procedures are implemented explicitly rather than delegated
to numerical epsilons or a different triangulation algorithm.

| Prerequisite | Source | Implemented resolution |
|---|---|---|
| Visibility map to triangulation | Paper references [6], [11]: [Chazelle–Incerpi (1984)](https://doi.org/10.1145/357337.357340), [Fournier–Montuno (1984)](https://doi.org/10.1145/357337.357341); [Toma lecture](https://tildesites.bowdoin.edu/~ltoma/teaching/cs3250-CompGeom/spring18/Lectures/cg-polygontriangulation.pdf) | `reduction` joins original cap generators, builds bounded-degree rotations, and triangulates monotone mountains with a strict-turn stack; collinear original vertices remain |
| Linear-time planar separator | Reference [21]: [Lipton–Tarjan (1979)](https://doi.org/10.1137/0136016), [primary technical report](http://i.stanford.edu/pub/cstr/reports/cs/tr/77/627/CS-TR-77-627.pdf); recursive use [22] | `separator` implements weighted BFS-level contraction and fundamental-cycle shrinking, with internal zero-weight face hubs and disconnected-component handling |
| Distinct-y input | Geometry/boundary spec §2 | `input` implements exact affine normalization; arithmetic bit costs remain separate; simplicity and pairwise distinctness are caller preconditions, not hash-validated |
| Boundary and shielding cases | §§2.1, 2.5; startup pp.503–504; search pp.509–510 | `cap` separates source/contact roles; `fusion` applies outgoing-germ transitions at startup and shared-level endpoint events; `witness` descends one saved child using full-boundary cyclic cuts |
| Temporary exit-edge deformation | §4.2 p.519, Fig.4.1; geometry/boundary spec §10 | Lazy offsets, clockwise nested collars, finite-only shear and route-preserving projective bridges; descriptor-aware saved queries, directed quotient, exceptional remote-cut repair and checked +2 original arc allowance |
| Arithmetic domain and storage updates | Geometry and normal form throughout | Rational and hierarchical symbolic exact scalars; normalized Vertex level sources, primitive contact rebasing, actual contraction weights, compact nested storage and linear current-map publication |
| Closed seam and power-of-two padding | §2.4 p.497; §4 p.516; geometry/boundary spec §8 | `input` pads/seams; `closure` restores original boundary darts and emits complete interior cells with borrowed original points and original cap-generator IDs |

The separator procedure was analyzed from the primary technical report. The
1984 reduction journal PDFs were not fully readable; the implemented mountain
reduction is corroborated by detailed lecture procedures and published
[Graphics Gems code](https://raw.githubusercontent.com/erich666/GraphicsGems/master/gemsv/ch7-5/monotone.c),
not claimed as a line-by-line transcription of those journal articles.

There is no ear-clipping, sweep, scanning-oracle or retry fallback on the public
path. Component errors propagate with their stage; they are not converted into
plausible triangles. The implementation remains a source-derived Rust algorithm,
not a Dafny proof or a claim of linear bit complexity.
