# Geometry and double-boundary specification

This specifies the geometry/boundary layer after [PAPER_MAP.md](PAPER_MAP.md).
Its rational and symbolic curve kernels are used by the complete Rust
triangulator. **Paper facts** are cited to Chazelle's
[1991 paper](https://www.cs.princeton.edu/~chazelle/pubs/polygon-triang.pdf);
**decisions and derivations** below are our implementation choices. Printed pages
490–491, 493–499, and 516 are the principal sources.

## 1. Input, coordinates, and ownership

**Decision:** accept exact rational coordinates, with integers as the denominator-1
case. Rust uses `num-bigint` and `num-rational`. No rounded floating-point
predicates, numeric epsilons, or coordinate-range-dependent overflow fallbacks.
The cost of big-integer arithmetic is separate from the paper's operation bound.

Polygon input is an ordered list of n ≥ 3 distinct vertices, with implicit last-to-
first closure. It must be simple, with nonzero edges and nonzero enclosed area.
Collinear consecutive edges are allowed when they do not overlap or backtrack.
There is no repeated closing vertex in the list. Simplicity and pairwise
distinctness are caller preconditions. Production checks reject zero-length
adjacent edges; neither an O(n²) validator nor expected-time hashing is hidden
in input preprocessing.

An open input curve has at least one edge. A zero-edge piece is a point/null arc,
not a visibility map of a curve. An open curve must also be simple and have no
repeated vertices.

Construct one immutable input table before building maps. It owns transformed
vertices, consecutive directed edges, vertex provenance, and edge provenance.
Maps refer to it by indices; grades never copy input slices. `OriginalVertexId`
is the output index in the caller's list. A synthetic vertex has a construction
provenance instead, never a fabricated original index.

Curve-local temporary exit edges used by refinement are separate descriptors
referencing existing endpoints. They do not mutate the global input table or
pretend to be adjacent global input edges. They need their own local edge ordering
when the refinement layer is implemented.

## 2. Original-input distinct y by exact affine normalization

**Paper fact:** the main construction assumes distinct vertex y-coordinates
(p.488); the paper cites symbolic perturbation for degeneracy handling.

**Decision:** for exact rational original input, satisfy this assumption using one
finite, orientation-preserving affine map. This avoids symbolic epsilon
arithmetic for that preprocessing step without changing the polygon's incidences.

Let W = max(xᵢ) − min(xᵢ), and let B be the largest positive denominator of any
input y-coordinate, in reduced form. Define:

- K = (W + 1) B²;
- X = x;
- Y = K y + x.

Compute W and B by a linear scan. Store transformed coordinates once. The inverse
is x = X, y = (Y − X)/K; triangle output uses original vertex IDs, so normally no
coordinate inversion is needed.

**Derivation:** if two rational y-coordinates differ, their distance is at least
1/B². Hence K|Δy| ≥ W + 1 > |Δx|. Their transformed Y-order agrees with their
original y-order. When y is equal, Y-order is x-order. Distinct input points
therefore have distinct Y, and every transformed input edge is nonhorizontal.
The determinant is K > 0: simplicity, orientation, collinearity, and containment
are preserved. Visibility is computed horizontally in (X,Y), not in the caller's
original coordinates; this is sufficient for triangulating the same polygon.

This normalization does not separate overlapping edges or repair invalid input.
It also does not eliminate the paper's conceptual double boundary: that is a
separate topological device, with no numerical thickening (p.490).

All subsequent synthetic input vertices are chosen with distinct Y (§8).
Temporary refinement exit edges are horizontal in this chart. The paper
symbolically tilts them before merging (p.519, Fig.4.1); the ordinary merge is not
specified to accept horizontal input edges unchanged. Section 10 gives the
implemented local deformation, consistent predicates, and limiting-cut reversal.
The global affine transform is
not a replacement for it, and must not be reapplied independently to regions
whose queries use saved maps in the existing chart.

## 3. Curve-local boundary identity

A map is scoped to a named connected input interval C = vₐ,…,vᵦ, a < b. The same
input vertex can be interior to one curve and an endpoint of another. Its boundary
occurrences are therefore **curve-local**, not globally interned by vertex ID.

Use conceptual identifiers with these fields:

| Entity | Required identity | Coordinate equality does not merge |
|---|---|---|
| Intrinsic boundary vertex | Curve ID, input vertex ID, side, local slot | Companions; extremum duplicates; endpoint caps |
| Interior boundary point | Curve ID, input edge ID, exact parameter t, side | Opposite sides of an edge |
| Map endpoint | Map ID and endpoint ID, referencing one of the above sites | Endpoints belonging to different maps |
| Chord | Map ID, two endpoints, route kind | A null chord versus a wrapping chord at the same coordinates |

An edge parameter is always measured along the forward input edge, even on the
reverse-traversed side. Normalize t = 0 or 1 to the corresponding curve-local
vertex occurrence, selecting the incoming/outgoing slot where required. Do not
retain two representations of one boundary occurrence. Interior points have
0 < t < 1. Normalization needs incidence information, not just coordinates.

`Left` and `Right` mean sides of the **forward directed curve**. Clockwise order
around its thin boundary is:

1. Left side, from curve start to curve end.
2. End cap, from Left to Right.
3. Right side, from curve end to curve start.
4. Start cap, from Right to Left.

Null cap and corner transitions have zero geometric length but remain ordered
boundary transitions. The exterior is on the walker's left, matching p.491.

## 4. Occurrence table, companions, and chord directions

For an interior vertex, let sᵢ = sign(Yᵢ − Yᵢ₋₁) and
sₒ = sign(Yᵢ₊₁ − Yᵢ). Both signs are nonzero. It is an extremum precisely when
sᵢ ≠ sₒ. Let T be the sign of orient(vᵢ₋₁,vᵢ,vᵢ₊₁).
At an extremum, simplicity excludes a collinear reversal, so T ≠ 0.

| Local case | Left occurrences in forward order | Right occurrences in reverse order | Companion pairing |
|---|---|---|---|
| Interior, sᵢ = sₒ | `Single` | `Single` | Left ↔ Right |
| Interior extremum | `Incoming`, `Outgoing` | `Outgoing`, `Incoming` | Incoming ↔ Outgoing **on each side separately** |
| Curve start | `Single`, using outgoing edge | `Single`, using outgoing edge | Left ↔ Right across start cap |
| Curve end | `Single`, using incoming edge | `Single`, using incoming edge | Left ↔ Right across end cap |

**Paper fact:** p.490 defines two companion pairs at an extremum, one pair on each
side. They are also adjacent duplicates. They are not paired across sides. This
corrects the cross-side wording in the initial paper map.

Directions are signs d ∈ {−1,+1}, for left/right in X:

| Site | Direction |
|---|---|
| Left side of an edge with Y-sign s | −s |
| Right side of that edge | +s |
| Extremum `Incoming` slot | Apply its side rule to the incoming edge |
| Extremum `Outgoing` slot | Apply its side rule to the outgoing edge |
| Ordinary interior singleton | Either adjacent edge gives the same answer |
| Endpoint singleton | Apply its side rule to its sole incident edge |

**Derivation:** the left normal of a clockwise edge walk points to the exterior.
Its horizontal component is minus the edge's Y-increment. On Right the walk is
reversed. At an extremum, the two slots on each side have opposite directions.

The side inside the turn is Left when T > 0 and Right when T < 0. Its duplicate
pair is joined by the intrinsic **null chord** (p.490). The other pair launches
nonnull rays. Companion is an involution with no fixed points; it is not the
operation for crossing an arbitrary chord.

Examples in transformed coordinates:

| Triple | Classification | Inside null pair | Left slot directions |
|---|---|---|---|
| (0,0), (1,2), (2,4) | Ordinary collinear | None | −1 for Single |
| (0,0), (1,2), (2,0) | Maximum, right turn | Right | Incoming −1; Outgoing +1 |
| (2,0), (1,2), (0,0) | Maximum, left turn | Left | Incoming −1; Outgoing +1 |
| (0,2), (1,0), (2,2) | Minimum, left turn | Left | Incoming +1; Outgoing −1 |
| (2,2), (1,0), (0,2) | Minimum, right turn | Right | Incoming +1; Outgoing −1 |

## 5. Horizontal intersections and spherical routes

For edge A→B and query level L, an intersection exists exactly when L lies in the
closed interval between A.Y and B.Y. With ΔY ≠ 0:

- t = (L − A.Y)/(B.Y − A.Y);
- Xhit = A.X + t(B.X − A.X).

For a clipped target arc, t must also belong to its exact clipped interval.
Endpoint intersections retain the incidence slot. Do not globally deduplicate
coincident vertex contacts: distinct boundary occurrences can have the same Xhit.
A shared arc endpoint is enumerated once per boundary occurrence, not once per
adjacent supporting edge.

For comparisons, use exact rational signs or positive-denominator cross-products.
No approximate division is allowed. A persistent hit identifies the input edge
and t, or a normalized vertex occurrence; cached Xhit is optional, not a second
source of identity.

**Paper fact:** (−∞,Y) and (+∞,Y) are identified (p.489). A level line is a circle,
not a line with two independent outside regions. Use three distinct route kinds:

| Route | Meaning | Equal-coordinate endpoints |
|---|---|---|
| Finite | A positive-length interval in the finite chart | Not permitted |
| Wrap | Complementary interval passing through horizontal infinity | Permitted: a full circuit joining distinct occurrences |
| Null | Intrinsic inside-turn pair, with zero geometric length | Required |

A right-going query first considers Xhit > Xsource in ascending order. Only if
there is no such contact does it wrap and consider contacts from the smallest X
up through Xsource. A left-going query first considers Xhit < Xsource in descending
order, then wraps from the largest X down through Xsource. A return at the source
coordinates can hit a **different** boundary occurrence after a full circuit.
It is not automatically a no-hit answer or a null chord.

Null-pair visibility is resolved by the occurrence table before a nonnull ray
query. Equal-coordinate contacts at departure are resolved by the local slots and
sides, never by a positive epsilon distance. A contact that the ray approaches
from the exterior must have an outward direction opposite the ray's direction.
At corners, use the incoming/outgoing slot and its sector; coordinates alone do
not select it.

Separate two operations:

- **Geometric contact:** closest intersection with a specified arc/subarc and
  route, with all tied boundary incidences retained until local classification.
- **Visibility decision:** check departure/arrival sectors and any blocking arcs
  required by the caller's local region/fusion invariant.

The §3 oracle targets a particular subarc; it does not certify global visibility.
An inadmissible nearest contact is not permission to skip through an intervening
boundary and return a farther visible-looking point. Fusion's reverse shooting
and shielding remain separate algorithmic obligations.

A canonical chord stores a route once; it must not infer Finite versus Wrap from
endpoint coordinates on each use. Reversal swaps endpoints and query direction
but preserves the geometric route. For a Null route, only its declared intrinsic
pair is valid. Regions at horizontal infinity need no allocated infinite vertex.

## 6. Arc order, spans, and weights

A boundary arc is a directed clockwise interval with exact start/end sites. Store
first/last supporting edge and side as in pp.497–498; chords own its endpoint
locations. Also distinguish an empty interval from a full boundary circuit.
The no-chord map has one region and the whole double boundary, not an empty arc.

Canonical order is implicit: Left sites increase in input index and t; Right
sites decrease. At an extremum, use the slot order in §4. Caps order the two
sides. No grade needs a copied list of all boundary occurrences. At a fixed input
edge, retained endpoints are ordered exactly by t on that side; double
identification uses the map's canonical arc indexes, not a scan of input vertices.

An arc can cross either or both endpoint caps. Decompose its interval into at
most three monotone side runs, without allocating an edge list. Each cap occurs
at most once in an interval no longer than a full circuit. Do not assume every
double-backing arc consists of exactly two runs.

For each run, normalize away zero-length leading/trailing pieces. Count one
nonnull edge for each positive-length piece of an input edge in that run. Sum
run counts; the same input edge visited on both sides counts twice. Null corners
and caps count zero. Region weight is the **maximum arc count**, or zero for an
empty region (p.494). Opposite-side endpoints never subdivide this side's arc.

Insertion can split one positive edge piece into two pieces across two new arcs.
Deleting its nonintrinsic endpoint joins them back into one. Consequently the
weight of a contracted region must be calculated from its normalized new arcs,
not by adding cached old region weights. Run endpoints and input index arithmetic
must support this calculation in constant many geometric operations per arc;
rescanning γ input edges on every contraction is not acceptable.

## 7. Mutation contracts for the normal-form kernel

These are topology contracts, not a prescription to recompute visibility by
brute force. Region/arc/chord adjacency must be explicit and map-local.

| Operation | Preconditions | Required transition |
|---|---|---|
| Insert a chord | Distinct unoccupied boundary sites; same Y; valid route; open route lies in one region; Null only for its intrinsic pair | Split that region and its affected arcs; add one dual-tree edge; allocate interior endpoints only when needed; preserve cyclic order |
| Delete a chord | A retained chord joining two regions | Contract its dual-tree edge; splice arcs in boundary order; remove now-unoccupied nonintrinsic endpoints; retain intrinsic occurrences, null transitions, and provenance |
| Coarsen | Conformal, semigranular map; target γ no smaller than current bound | Remove only chords with a degree-<3 incident node and actual contracted weight ≤ γ; maintain degree ≤4 |
| Build a decomposition | Conformal map | Internal nodes identify retained chords; leaves identify all regions, including empty ones; each split obeys the three-quarters bound |
| Query double identification | Named input point on an edge and a normal-form map | Return its side-aware containing arcs, including corner/cap cases; at most six results; logarithmic search, no allocation per result list |

An intrinsic occurrence can become unoccupied after chord deletion; it stays in
the implicit boundary. It has exactly one chord in the **full** visibility map,
not necessarily in a submap. A retained chord endpoint cannot simultaneously be
claimed by two chords. Empty regions and null chords are never silently erased
because they have zero geometric area or length.

Canonical arc indexes and the binary decomposition are invalid after a mutation
that changes their topology. Use a construction state without query access while
merging, then reconstruct normal form at the paper's charged cost. Do not expose
stale queries or add a general dynamic-tree requirement.

Publication compacts live outer arenas **and** every surviving region's arc/exit
vector capacity; coarse saved maps must not retain storage from a finer map.
Map-local IDs expire during this republication. Coarsening rechecks at most four
surviving neighbors after each contraction, preserving the degree/actual-weight
predicate while handling degree eligibility changed by null-leaf deletion.

### Joining two curve scopes

Let C₁ end where C₂ begins. Copying endpoint occurrence IDs into the result is
wrong: the common vertex is now interior. The remapping is:

- Nonextremum union: both input endpoint occurrences on a given side map to the
  union's one singleton on that side.
- Extremum union: the C₁ endpoint on a side maps to Incoming; the C₂ endpoint
  on that side maps to Outgoing. The new inside pair is the null pair.

Other input vertices retain their side and slot, but acquire the output curve
scope. This remapping describes identity, not chord survival. Fusion startup
(pp.503–504) must still determine the common-vertex chords and reconcile
coincident candidates; it cannot retain two chords on a newly coalesced singleton.
Input maps remain unchanged while the output is constructed.

## 8. Closed seam, padding, and reversal

**Paper facts:** p.497 permits puncturing a small hole to make the curve open;
p.516 permits padding to 2^p + 1 vertices. The following exact construction is our
choice; no numerical infinitesimal is required.

After the affine transform, choose original edge v₀→v₁. Let s be the sign of
Y₁ − Y₀. A linear scan gives
δ = minᵢ≠₀ |Yᵢ − Y₀| / 4 > 0. All coordinates with Y = Y₀ + s q for
0 < q ≤ δ lie in a vertex-level-free corridor along this edge.

Choose seam endpoints A and B on that edge at:

- Y(A) = Y₀ + s δ/2;
- Y(B) = Y₀ + s 3δ/4.

Remove the relatively open segment A→B. The open curve follows
B, v₁,…,vₙ₋₁,v₀, A. It has n + 2 vertices and retains every original vertex
with both original incident directions.

Let p be minimal with 2^p ≥ n + 1, and let r = 2^p + 1 − (n + 2).
Add r padding points on the v₀→A stub at levels
Y₀ + s δ j/(4(r + 1)), j = 1,…,r, in forward edge order.
There are now exactly 2^p + 1 vertices, all with distinct Y. Padding, A, and B lie
in disjoint level intervals; no original vertex level intersects the seam gap.
Obtain X and the original-edge parameter by exact interpolation. All synthetic
points are collinear with the original edge, and the open curve remains simple.
The number of vertices is O(n); constructing the table is a linear number of
exact arithmetic operations.

For an already-open curve, use the same vertex-level-free corridor at its first
edge for padding, without introducing a seam. Choose p minimal with 2^p ≥ its
edge count, and insert the required number of distinct interior points before the
next vertex level. For example, use qⱼ = δ j/(2(r + 1)). The endpoints do not move.

**Reversal contract:** complete the open curve's full visibility map, including
all intrinsic original-vertex chords. At any original vertex level, the gap is
absent and the union of subdivided edge pieces is exactly the original closed
edge set. The geometric first contacts and local original-vertex sectors are
therefore unchanged by opening/padding.

Retain the chords incident to original intrinsic occurrences, including original
null pairs; discard synthetic-vertex and other augmentation chords. Relabel all
retained edge contacts using the original edge ID and exact parameter. After
deletion, both seam caps border the same region: there is no retained chord at
a level inside the gap. Replace the A and B cap connections by the Left A→B and
Right B→A boundary connections. This splits that seam region into interior and
exterior regions. Splice collinear stubs into the original edge, eliminate
padding/cap occurrences, and trace the new region boundaries in linear
retained-feature work. The double boundary now has two closed cycles.

The open map's dual-tree invariant must **not** be asserted after closure:
interior and exterior are separated again. The closed visibility structure is
then the input to the separately required linear triangulation reduction.

This specifies seam geometry and the preservation argument, not the external
triangulation algorithm. The reduction must accept this closed visibility
structure and preserve collinear original vertices without synthetic output IDs;
that source dependency remains open.

## 9. Rust implementation boundary and acceptance

Use distinct typed indices for input vertices/edges, curve scopes, and map-owned
arcs/chords/regions. Use enums for Side, Slot, Direction, and Route. Exact rational
edge parameters belong only to inserted endpoints and synthetic input vertices;
intrinsic original occurrences are recovered from their IDs and local class.

Do not allocate complete boundary-vertex tables for every chain. Store global
edge Y-signs once and derive chain-local occurrences from the two endpoint
indices and at most the adjacent edges. Iterate side runs lazily. A fixed-capacity
six-entry result is sufficient for double identification. Reuse arithmetic
scratch where the chosen numeric library permits; normalize persistent values,
not every transient comparison by default. Arithmetic scratch is not shared
across simultaneously active maps without an explicit owner.

The kernel supports these consumer-visible cases:

- Equal original y and horizontal original edges become a coherent exact strict
  Y-order, without changing orientation or introducing crossings.
- Every ordinary vertex/endpoint has two occurrences; every interior extremum
  has four with the correct same-side companion pairs and inside null chord.
- Reversing a curve exchanges Left/Right and Incoming/Outgoing consistently.
- Finite, full-circuit wrapping, and null chords remain distinct at coincident
  coordinates; clipped-arc hits preserve local identity.
- A common-vertex join normalizes endpoint identities by the union's local class.
- Deleting a chord removes only nonintrinsic endpoints and computes actual new
  arc weights, including an arc crossing both caps.
- Seam/padding introduces no equal Y, preserves original-level intersections,
  and never leaks a synthetic original-vertex ID.

The kernel now executes these transitions with exact rational geometry. The
closed-map path accepts borrowed original point tables and emits nondegenerate
CCW original-ID triangles; it does not copy the input geometry into the reducer.
`base::full_visibility` is restricted to a fixed 16-edge leaf, not a scanning
fallback for arbitrary curves. Common-vertex source/contact flags, fusion,
one-child shielding, and region-local symbolic refinement share the same
`Curve`/`ExactScalar` boundary and sparse topology. The public `triangulate` API
constructs full visibility before the borrowed closed-cell reduction.

## 10. Temporary local geometry for down-phase refinement

**Implemented derivation:** `view`, `program`, `ribbon`, `program_queries`,
`collapse`, `graft`, and `triangulation` realize the p.519 tilt for coincident caps,
repeated opposite-side arcs, null transitions and exits through horizontal
infinity. These are explicit bounded-description curve extensions, not a
line-by-line transcription of the paper's unspecified perturbation.

### 10.1. Directed local boundary

- Traverse the actual old face word with `Submap::arc_successor`, not the stored
  region vector's incidental order: a clockwise original arc is followed by its
  exit dart to the mate. The old region lies on this directed word's Left.
- Give each R-facing side run a lazy normal lane. For forward edge vector d,
  use N = (−dy, dx)/(|dx| + |dy|) and support p + sδN + td, with positive width
  on Left and negative width on Right. Genuine-turn vertices are intersections
  of shifted supports; positive collinear continuation shares one normal.
  Evaluation uses only constant-many Root neighbors, never a copied chain.
- Physical stars include exit endpoints, relevant caps and **every opposite-side
  R-facing transit at the same point**, including edge-interior occurrences.
  Preserve their original Side/Slot/germ labels separately from coordinates.
- Trim on disjoint formal rational diamonds. Each trimmed original branch stays
  on its known incident Root edge; positive-length stubs remain Original aliases.
  No other Root vertex lies in such an infinitesimal collar.
- Connect incoming to outgoing ports clockwise in the inherited R-sector:
  short convex, long reflex, or nearly full same-germ cap. Noninterleaving port
  intervals are disjoint or nested; containing intervals receive deeper collars.
  Split at diamond corners. Straight independent endpoint slides can overlap
  same-germ cap branches and are not used.
- These selected Left-side aliases and collar sector tokens form a monotone,
  directed quotient onto the old region boundary word. Open the programme only
  by puncturing a constant-size helper piece, never a positive original alias.

### 10.2. Finite chart, wrapping bridges and source levels

- Apply the common lower-order Y → Y + ηX to finite supports and collars only.
  An unbounded affine shear at horizontal infinity has incompatible seam limits.
- Compact with U = X/(1 + |X|). A protected Wrap bridge interpolates U and Y on
  its proper unwrapped interval, folds at most once, and keeps a shared seam
  token. A pre-seam auxiliary vertex separates its seam level from vertex levels.
  Equal-coordinate full returns retain distinct terminal occurrence roles.
- `Symbolic` is an exact rational-function field with 128 hierarchical positive
  infinitesimals. Coefficients and polynomials share storage; normal exponents
  are inline, with arbitrary-precision promotion on overflow. Sign and equality
  use algebraic values, never variable IDs as geometric tie breakers.
  Ordering compares exact leading monomial/coefficient products first. Tied
  products stream all equal-monomial coefficient groups exactly, stopping only
  at the first nonzero difference; equality exhausts both streams.
- A retained chord carries `LevelSource::Vertex` or `Frozen`. The generic kernel
  supports arbitrary certified frozen augmentations. Production refinement
  requires normalized Vertex sources: bounded leaves use actual Programme
  vertices, fusion inherits/promotes sources, and witnesses preserve them.
  `Ribbon::root_source` maps each source arithmetically to its Root base vertex.
- Reevaluate symbolic Edge contacts from the supporting primitive and that
  actual source level before further fusion. Old rational parameters and old
  Wrap levels are not displaced clipping thresholds; saved probes compare
  reevaluated endpoints and source levels without rebuilding saved topology.
  This prevents recursive Contact(Contact) expressions across merge depth.
- Alias/helper primitives have bounded description and algebraic depth. Every
  local programme disappears after collapse; exact coefficient/bit costs are
  not asserted to be constant.

### 10.3. Exceptional limiting cuts

A helper's geometry may be local while its visibility contact is remote: the
bottom of the start-cap collar for (0,0) → (0,2) → (4,3) → (4,−2) sees x = 4,
with limiting contact (4,0). Discarding helper chords and repairing only erased
intrinsic vertices would lose that remote original-arc cut.

`collapse` instead:

1. Retains authoritative old exits and their occurrence/source/route identities.
2. Keeps ordinary legal Original2 limits using the directed quotient, exact
   support residues, and Side/Slot normalization—not coordinate deduplication.
3. Includes the actual Root Vertex(q) source of each old exit in its exceptional
   packet, even if q is remote and neither exit endpoint is intrinsic.
4. Queues each original endpoint of a discarded helper-incident or exceptional
   invalid limiting chord, and **all original star transit occurrences**.
5. Repairs each cut independently in its actual Root direction. Inside Nulls
   resolve immediately; occupied authoritative exits keep their partners.
   Otherwise query at most four immutable old R-arcs, retain the first raw
   physical blocker and all tied flags, and select the correct outside arrival.
   Never skip a wrong-sector nearest blocker to return a farther contact.
6. Deduplicates by actual endpoint identities and route, rejecting conflicting
   mates. Per-old-arc streams retain transported cut order; only constant-size
   repair additions are sorted. Identical repaired endpoint references occur
   once; distinct duplicate-pair rows retain the ordered builder's coverage.
7. Grafts through linear cyclic assembly, then restores conformality and
   contracts using actual Root arc weights.

Independent repair starts in the old R-facing germ. Its horizontal prefix cannot
cross a horizontal protected exit transversely; the first collinear entry is an
original endpoint and thus a blocker. It stays in the named old region until the
first original contact. There is no need to continue a limiting route through
an occupied or opposite-side occurrence to connect its former two endpoints.

The expensive repairs are bounded by constant-many stars, helper pieces and
exceptional actual levels. At one exact level retained positive visibility
intervals have disjoint interiors, so only constant-many can contain a fixed
exceptional blocker/germ. This does **not** assume a bounded number of chords per
Vertex source class. Ordinary retained endpoints receive no repair query.

### 10.4. Original arc bound and publication

Every selected original cut survives as a kept chord, protected exit or repaired
cut at the same original occurrence. Every R-facing star transit is also a cut.
Consequently a final positive Root arc has no star internally, and its directed
core lies in one temporary predecessor support arc. Alias projection preserves
Side and injects those Root edge visits into temporary support-edge visits.
Only the two endpoint collars can add an unrepresented trimmed Root edge:

`weight_Root <= weight_temporary_support + 2`.

Restoration adds cuts and cannot increase this bound. The controller checks it
before contracting at `gamma_next = canonical_gamma(gamma) + 2`, where
`canonical_gamma(gamma) = 2^ceil(ceil(log2(gamma))/5)`. This strictly decreases
for gamma > 16. At the fixed cutoff, `completion` reconstructs every original
intrinsic visibility chord by bounded region enumeration; gamma = 1 alone does
not guarantee full visibility.

Saved maps retain query decompositions. Current/final visibility publication
follows physical endpoint links to canonical order in linear time, compacts all
nested capacities, and does not build an unused balanced decomposition. These
are source-derived implementation invariants, not a machine-checked proof or
a linear big-integer bit-cost claim.
