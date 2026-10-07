# Geometry and double-boundary specification

This specifies the geometry/boundary layer after [PAPER_MAP.md](PAPER_MAP.md).
Its rational input and normal-form kernel are implemented in Rust; this is not
yet a complete triangulator. **Paper facts** are cited to Chazelle's
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
specified to accept horizontal input edges unchanged. That local deformation,
its consistent predicates, and its reversal require a separate constructive
specification before implementing refinement. The global affine transform is
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

The first kernel must support these consumer-visible cases:

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
fallback for arbitrary curves. Common-vertex source/contact flags are executable,
but full fusion, shielding, and symbolic down-phase integration remain required.

## 10. Temporary local geometry for down-phase refinement

**Derived contract, not implemented:** the p.519 tilt must support coincident
caps, repeated opposite-side arcs, null transitions, and exits through horizontal
infinity without changing or rebuilding saved original-chain maps.

- Give each R-facing side run a lazy normal lane. For forward edge vector d,
  use N = (−dy, dx)/(|dx| + |dy|) and support p + sδN + td, where s is +1 on
  Left and −1 on Right. Interior vertices are intersections of adjacent shifted
  supports; positive collinear continuation uses the shared normal directly.
  Vertex evaluation uses only its constant-many neighbors.
- At constant-many junctions, trim branches on a formal rational diamond and
  route paired lane ports through an inner collar in their inherited ribbon
  rotation. Nested port intervals get nested collar heights. Straight independent
  endpoint slides are insufficient: coincident cap ports with the same original
  germ can produce an overlapping bridge.
- Apply a common lower-order Y → Y + ηX only to finite supports and collars.
  Applying that shear across horizontal infinity would give incompatible seam
  limits. Instead compact U = X/(1 + |X|), interpolate U and Y along an unwrapped
  route-preserving bridge, and fold at most once at the seam. One seam token
  identifies both representations of the same crossing.
- A retained chord needs a normalized common level descriptor: a displaced
  original-vertex level when inherited from one, or a frozen exact rational
  level for an arbitrary augmentation. New contacts inherit this descriptor,
  not a recursively embedded intersection expression. Equal physical
  subdivisions share their level program.
- Reevaluate nonintrinsic retained endpoints from their shifted supporting edge
  and common level. Old rational parameters and old rational Wrap levels are
  not valid symbolic clipping thresholds. Saved decomposition/separator topology
  can be reused only with descriptor-aware endpoint and level comparisons.
- Preserve source occurrence, side/slot, route, and OriginalArc/ProtectedExit/
  Collar/Bridge/Seam provenance through collapse. Cancel common factors before
  limits; coordinate deduplication alone cannot distinguish a cap, intrinsic
  Null, and a full-circle Wrap.
- Keep authoritative old exits. A discarded helper separator can have a remote
  original-support contact: the bottom of a start-cap collar for
  (0,0) → (0,2) → (4,3) → (4,−2) sees x = 4, with limiting contact (4,0).
  Consequently, locality of the helper's source does **not** imply locality of
  its other endpoint. Repairing erased intrinsic occurrences alone is not yet
  an arc-weight proof.
- Before discarding a separator, require a replacement correspondence: an
  authoritative protected exit or regenerated original-side separator must
  preserve each nonlocal original-arc cut, with the correct side/slot and route.
  Coincident blockers may require partitioning its limiting route into legal
  original visibility intervals; merely checking its two endpoint labels is
  insufficient. A bounded replacement-chain argument is still a proof gate,
  including augmentations whose level coincides with an original vertex.
- Restore conformality **after** quotient/filtering and those replacements.
  Conformality alone cannot fix an oversized arc in a region with at most four
  exits. Publish only after actual original positive-length arc weights satisfy
  the refinement scale; a full-chain scan is not an admissible repair.
- Each local program has constant-many symbolic priorities and bounded
  expression depth; it is discarded after collapse. Saved geometry is neither
  scanned nor copied. These are constraints on the intended geometric-operation
  ledger, not an implemented refinement or a linear big-integer bit-cost bound.
