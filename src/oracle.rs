//! Separator ray shooting on the collapsed spherical subdivision (§3.4).
//! Preprocessing touches retained records only; queries scan original arc pieces.
//! The owned map must be compact, conformal and gamma-granular. Collapsed
//! degree-two curve bends stay implicit, whereas nonnull wrapping loops stay
//! explicit even when their faces have zero boundary-arc weight. Construction
//! costs O(mu log m); separator and residual scans cost
//! O(gamma * ceil(mu^(2/3)) + log m) geometric operations per query.
//! Curves supply actual tangent germs and a bounded chart-cut catalogue.
//! Retained endpoint and far-right level sources survive preprocessing so a
//! probe of a topology-stable saved view can reevaluate its displaced contacts;
//! establishing that view's topology stability is the caller's obligation.
use std::cmp::Ordering;
use std::fmt;
use crate::boundary::{Arc, Boundary, BoundaryError, Position, Side, Site, Slot};
use crate::curve::{Curve, LevelSource};
use crate::geometry::{Direction, Rational, Route, ray_order};
use crate::input::{EdgeId, Input, VertexId};
use crate::separator::{Dart, EmbeddedGraph, Separator, SeparatorError};
use crate::submap::{MapError, RegionId, Submap};
use crate::work::Work;
use crate::scalar::ExactScalar;

/// A query in the oracle's curve or a topology-stable displaced view.
pub trait RayProbe<C: Curve = Input> {
    type Hit: Clone;
    fn edge_hit(&self, input: &C, edge: EdgeId, work: &mut Work) -> Option<Self::Hit>;
    fn edge(&self, hit: &Self::Hit) -> EdgeId;
    fn parameter_cmp(&self, hit: &Self::Hit, t: &C::Scalar) -> Ordering;
    fn compare_hits(&self, a: &Self::Hit, b: &Self::Hit) -> Ordering;
    fn compare_level(&self, y: &C::Scalar) -> Ordering;
    /// Compare against the retained endpoint without discarding its source.
    /// A displaced probe reevaluates this source on the supporting edge.
    fn compare_endpoint(&self, _input: &C, hit: &Self::Hit, endpoint: &Site<C::Scalar>, _source: &LevelSource<C::Scalar>) -> Ordering {
        match endpoint {
            Site::Edge { t, .. } => self.parameter_cmp(hit, t),
            Site::Vertex { vertex, .. } => self.parameter_cmp(hit, &if vertex.0 == self.edge(hit).0 { C::Scalar::zero_value() } else { C::Scalar::one_value() }),
        }
    }
    fn compare_source_level(&self, input: &C, source: &LevelSource<C::Scalar>) -> Ordering {
        self.compare_level(input.level(source).as_ref())
    }
    fn direction(&self) -> Direction;
}

#[derive(Clone, Debug)]
pub struct PointProbe<S = Rational> { pub x: S, pub y: S, pub direction: Direction }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PointHit<S = Rational> { pub edge: EdgeId, pub t: S, pub x: S }
impl<C: Curve> RayProbe<C> for PointProbe<C::Scalar> {
    type Hit = PointHit<C::Scalar>;
    fn edge_hit(&self, input: &C, edge: EdgeId, work: &mut Work) -> Option<Self::Hit> {
        work.predicates += 1;
        let (t, x) = input.horizontal_hit(edge, &self.y)?;
        Some(PointHit { edge, t, x })
    }
    fn edge(&self, hit: &Self::Hit) -> EdgeId { hit.edge }
    fn parameter_cmp(&self, hit: &Self::Hit, t: &C::Scalar) -> Ordering { hit.t.cmp(t) }
    fn compare_hits(&self, a: &Self::Hit, b: &Self::Hit) -> Ordering { ray_order(&self.x, self.direction, &a.x, &b.x) }
    fn compare_level(&self, y: &C::Scalar) -> Ordering { self.y.cmp(y) }
    fn direction(&self) -> Direction { self.direction }
}
#[derive(Debug)]
pub enum OracleError { Boundary(BoundaryError), Map(MapError), Separator(SeparatorError), InvalidGamma, NotConformal, NotGranular, InvalidEmbedding, InconsistentIncidence }
impl fmt::Display for OracleError { fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result { write!(f, "{self:?}") } }
impl std::error::Error for OracleError {}
impl From<BoundaryError> for OracleError { fn from(e: BoundaryError) -> Self { Self::Boundary(e) } }
impl From<MapError> for OracleError { fn from(e: MapError) -> Self { Self::Map(e) } }
impl From<SeparatorError> for OracleError { fn from(e: SeparatorError) -> Self { Self::Separator(e) } }

#[derive(Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
struct Place<S> { edge: usize, t: S }
impl<S: ExactScalar> Place<S> {
    fn site(site: &Site<S>) -> Self { match site {
        Site::Vertex { vertex, .. } => Self { edge: vertex.0, t: S::zero_value() },
        Site::Edge { edge, t, .. } => Self { edge: edge.0, t: t.clone() },
    } }
}
#[derive(Clone, Debug)]
struct WrapLevel<S> { source: LevelSource<S>, lower: RegionId, upper: RegionId }
#[derive(Debug)]
pub struct RayOracle<'a, C: Curve = Input> {
    map: Submap<'a, C>, gamma: usize, separator: Vec<bool>, groups: Vec<Vec<RegionId>>,
    membership: Vec<Option<usize>>, nonempty: Vec<bool>, wraps: Vec<WrapLevel<C::Scalar>>, exterior: RegionId,
    separator_regions: Vec<RegionId>,
}
impl<C: Curve> Clone for RayOracle<'_, C> {
    fn clone(&self) -> Self {
        Self { map: self.map.clone(), gamma: self.gamma, separator: self.separator.clone(),
            groups: self.groups.clone(), membership: self.membership.clone(), nonempty: self.nonempty.clone(),
            wraps: self.wraps.clone(), exterior: self.exterior, separator_regions: self.separator_regions.clone() }
    }
}

fn incidence<C: Curve>(map: &Submap<'_, C>, boundary: &Boundary<'_, C>, site: &Site<C::Scalar>, work: &mut Work) -> Result<[RegionId; 2], OracleError> {
    let arcs = map.canonical_arcs();
    if arcs.is_empty() { return Err(OracleError::InvalidEmbedding); }
    if map.arc_sites(arcs[0]).is_none() { let r = map.arc_region(arcs[0])?; return Ok([r; 2]); }
    let i = arcs.partition_point(|a| {
        work.predicates += 1;
        boundary.compare_sites(map.arc_sites(*a).unwrap().0, site) != Ordering::Greater
    });
    let j = if i == 0 { arcs.len() - 1 } else { i - 1 };
    let a = arcs[j];
    work.predicates += 1;
    let before = if boundary.compare_sites(map.arc_sites(a).unwrap().0, site) == Ordering::Equal { arcs[(j + arcs.len() - 1) % arcs.len()] } else { a };
    Ok([map.arc_region(before)?, map.arc_region(a)?])
}

// The rotations have at most four germs. Cross products compare their local
// tangents, never the chord of a bent curve interval.
fn angle<S: ExactScalar>(a: &(S, S), b: &(S, S)) -> Ordering {
    let half = |v: &(S, S)| v.1.sign() == Ordering::Greater || (v.1.is_zero_value() && v.0.sign() == Ordering::Greater);
    half(b).cmp(&half(a)).then_with(|| a.0.times(&b.1).minus(&a.1.times(&b.0)).sign().reverse())
}
fn add_edge<S>(rotations: &mut [Vec<usize>], ends: &mut Vec<usize>, labels: &mut Vec<RegionId>, tangents: &mut Vec<(S, S)>, a: usize, b: usize, left: RegionId, right: RegionId, ta: (S, S), tb: (S, S)) {
    let d = ends.len(); ends.extend([a,b]); labels.extend([left,right]); tangents.extend([ta,tb]);
    rotations[a].push(d); rotations[b].push(d+1);
}
fn collapsed<C: Curve>(map: &Submap<'_, C>, work: &mut Work) -> Result<(EmbeddedGraph, Vec<RegionId>, Vec<bool>, Vec<WrapLevel<C::Scalar>>), OracleError> {
    let boundary = Boundary::new(map.input(), map.chain())?;
    let mut places = vec![Place { edge: map.chain().start.0, t: C::Scalar::zero_value() }, Place { edge: map.chain().end.0, t: C::Scalar::zero_value() }];
    for c in map.chord_ids() { work.retained_visits += 1; let (s, _) = map.chord(c)?; places.extend(s.into_iter().map(Place::site)); }
    places.sort_unstable_by(|a,b| { work.predicates+=1; a.cmp(b) });
    places.dedup_by(|a,b| { work.predicates+=1; a==b });
    let mut rotations = vec![Vec::new(); places.len()];
    let mut ends = Vec::new(); let mut labels = Vec::new(); let mut tangents = Vec::new();
    let one = C::Scalar::one_value();
    let two = C::Scalar::from_usize_value(2);
    for i in 0..places.len()-1 {
        work.retained_visits += 1;
        let p = &places[i]; let q = &places[i+1];
        // A sample immediately after p suffices: no retained endpoint lies
        // inside this bent interval, even when it spans many input edges.
        let t = p.t.plus(if p.edge == q.edge { &q.t } else { &one }).over(&two);
        let sample = Site::Edge { edge: EdgeId(p.edge), t, side: Side::Left };
        let l = incidence(map, &boundary, &sample, work)?[1];
        let sample = match sample { Site::Edge { edge, t, .. } => Site::Edge { edge, t, side: Side::Right }, _ => unreachable!() };
        let r = incidence(map, &boundary, &sample, work)?[1];
        let first = map.input().edge_tangent(EdgeId(p.edge), &p.t);
        let previous = if q.t.is_zero_value() { q.edge-1 } else { q.edge };
        let last = map.input().edge_tangent(EdgeId(previous), if q.t.is_zero_value() { &one } else { &q.t });
        add_edge(&mut rotations, &mut ends, &mut labels, &mut tangents, i, i+1, l, r, (first.x,first.y), (last.x.negative(),last.y.negative()));
    }
    let mut wraps = Vec::new();
    for c in map.chord_ids() {
        work.retained_visits += 1;
        let (s, route) = map.chord(c)?;
        if route == Route::Null { continue; }
        let [a,b] = s.map(|site| places.binary_search_by(|place| {
            work.predicates += 1;
            match site {
                Site::Vertex { vertex, .. } => place.edge.cmp(&vertex.0).then_with(|| {
                    if place.t.is_zero_value() { Ordering::Equal } else { Ordering::Greater }
                }),
                Site::Edge { edge, t, .. } => place.edge.cmp(&edge.0).then_with(|| place.t.cmp(t)),
            }
        }).unwrap());
        let regions = map.chord_regions(c)?; let direction = boundary.direction(s[0])?;
        let dx = if direction == Direction::Right { C::Scalar::one_value() } else { C::Scalar::one_value().negative() };
        add_edge(&mut rotations, &mut ends, &mut labels, &mut tangents, a,b,regions[1],regions[0],(dx.clone(),C::Scalar::zero_value()),(dx.negative(),C::Scalar::zero_value()));
        if route == Route::Wrap {
            let (lower,upper) = if direction == Direction::Right { (regions[0],regions[1]) } else { (regions[1],regions[0]) };
            wraps.push(WrapLevel { source: map.chord_level(c)?.clone(), lower, upper });
        }
    }
    // The curve supplies a bounded catalogue, never an input-edge table.
    for cut in map.input().cut_crossings() {
        work.retained_visits += 1;
        if cut.edge.0 < map.chain().start.0 || cut.edge.0 >= map.chain().end.0 { continue; }
        work.predicates += 3;
        if cut.parameter.sign() != Ordering::Greater || cut.parameter.compare_one() != Ordering::Less || cut.forward == Ordering::Equal {
            return Err(OracleError::InconsistentIncidence);
        }
        let [left,right] = [Side::Left,Side::Right].map(|side| {
            incidence(map,&boundary,&Site::Edge { edge:cut.edge,t:cut.parameter.clone(),side },work)
        });
        let left=left?; let right=right?;
        if left[0]!=left[1] || right[0]!=right[1] { return Err(OracleError::InconsistentIncidence); }
        let (lower,upper)=if cut.forward==Ordering::Greater { (right[0],left[0]) } else { (left[0],right[0]) };
        wraps.push(WrapLevel { source:cut.level.clone(),lower,upper });
    }
    for rotation in &mut rotations {
        if rotation.len() > 4 { return Err(OracleError::InvalidEmbedding); }
        rotation.sort_by(|&a,&b| { work.predicates += 1; angle(&tangents[a],&tangents[b]) });
        for pair in rotation.windows(2) { work.predicates+=1; if angle(&tangents[pair[0]],&tangents[pair[1]]) == Ordering::Equal { return Err(OracleError::InvalidEmbedding); } }
    }
    let n = map.region_ids().count(); let mut nonempty = vec![false;n];
    let mut seen = vec![false;ends.len()]; let mut face_rotations = vec![Vec::new();n];
    for start in 0..ends.len() {
        if seen[start] { continue; }
        let region = labels[start]; let mut d = start;
        if nonempty[region.0] { return Err(OracleError::InvalidEmbedding); }
        loop {
            work.retained_visits += 1;
            if seen[d] || labels[d] != region { return Err(OracleError::InvalidEmbedding); }
            seen[d] = true; nonempty[region.0] = true; face_rotations[region.0].push(d);
            let r = &rotations[ends[d^1]];
            let j = r.iter().position(|&x| x == (d^1)).ok_or(OracleError::InvalidEmbedding)?;
            d = r[(j+r.len()-1)%r.len()];
            if d == start { break; }
        }
    }
    let regions: Vec<_> = map.region_ids().filter(|r| nonempty[r.0]).collect();
    let mut dense = vec![usize::MAX;n]; for (i,r) in regions.iter().enumerate() { dense[r.0]=i; }
    let mut edges: Vec<_> = (0..ends.len()).step_by(2).filter_map(|d| {
        let a=labels[d].0; let b=labels[d^1].0;
        (a!=b).then_some((a.min(b),a.max(b),d))
    }).collect();
    edges.sort_unstable(); edges.dedup_by(|a,b| a.0==b.0 && a.1==b.1);
    let mut graph = EmbeddedGraph { darts: Vec::with_capacity(2*edges.len()), rotations: vec![Vec::new();regions.len()] };
    let mut dual = vec![usize::MAX;ends.len()];
    for (_,_,d) in edges {
        let i=graph.darts.len();
        graph.darts.push(Dart { target: dense[labels[d^1].0], twin:i+1 });
        graph.darts.push(Dart { target: dense[labels[d].0], twin:i });
        dual[d]=i; dual[d^1]=i+1;
    }
    for r in &regions { graph.rotations[dense[r.0]] = face_rotations[r.0].iter().rev().filter_map(|&d| (dual[d]!=usize::MAX).then_some(dual[d])).collect(); }
    wraps.sort_by(|a,b| { work.predicates+=1; map.input().level(&a.source).cmp(&map.input().level(&b.source)) });
    for pair in wraps.windows(2) {
        work.predicates += 1;
        if map.input().level(&pair[0].source) == map.input().level(&pair[1].source) || pair[0].upper != pair[1].lower { return Err(OracleError::InconsistentIncidence); }
    }
    Ok((graph,regions,nonempty,wraps))
}

fn induced(graph: &EmbeddedGraph, nodes: &[usize], index: &mut [usize], remap: &mut [usize], work: &mut Work) -> EmbeddedGraph {
    for (i,&v) in nodes.iter().enumerate() { index[v]=i; }
    let mut darts=Vec::new(); let mut rotations=vec![Vec::new();nodes.len()];
    for (i,&v) in nodes.iter().enumerate() { for &d in &graph.rotations[v] {
        work.separator_visits += 1;
        let target=index[graph.darts[d].target]; if target==usize::MAX { continue; }
        remap[d]=darts.len(); rotations[i].push(darts.len()); darts.push(Dart { target,twin:graph.darts[d].twin });
    } }
    for d in &mut darts { d.twin=remap[d.twin]; }
    for &v in nodes { index[v]=usize::MAX; }
    EmbeddedGraph { darts,rotations }
}
fn partition(graph: EmbeddedGraph, regions: Vec<RegionId>, limit: usize, removed: &mut [bool], groups: &mut Vec<Vec<RegionId>>, work: &mut Work) -> Result<(),OracleError> {
    if regions.len() <= limit { if !regions.is_empty() { groups.push(regions); } return Ok(()); }
    let separator=Separator::build(&graph,&vec![1;regions.len()],work)?;
    for &i in &separator.removed { removed[regions[i].0]=true; }
    let mut index=vec![usize::MAX;graph.rotations.len()];
    let mut remap=vec![usize::MAX;graph.darts.len()];
    for component in separator.components {
        if component.len()==regions.len() { return Err(OracleError::InvalidEmbedding); }
        let residual=induced(&graph,&component,&mut index,&mut remap,work);
        let ids=component.into_iter().map(|i|regions[i]).collect();
        partition(residual,ids,limit,removed,groups,work)?;
    }
    Ok(())
}
fn threshold(n: usize) -> usize {
    let square=(n as u128)*(n as u128); let mut lo=1usize; let mut hi=n.max(1);
    while lo<hi { let m=lo+(hi-lo)/2; let cube=(m as u128).checked_mul(m as u128).and_then(|v|v.checked_mul(m as u128)); if cube.is_none_or(|v|v>=square) { hi=m; } else { lo=m+1; } }
    lo
}

impl<'a, C: Curve> RayOracle<'a, C> {
    pub fn build(map: Submap<'a, C>, gamma: usize, work: &mut Work) -> Result<Self,OracleError> {
        if gamma==0 { return Err(OracleError::InvalidGamma); }
        let boundary=Boundary::new(map.input(),map.chain())?;
        let n=map.region_ids().count();
        for r in map.region_ids() {
            work.retained_visits += 1;
            if map.region_exits(r)?.len()>4 { return Err(OracleError::NotConformal); }
            if map.region_weight(&boundary,r)?>gamma { return Err(OracleError::NotGranular); }
        }
        for c in map.chord_ids() {
            work.retained_visits+=1;
            let [a,b]=map.chord_regions(c)?;
            if (map.region_exits(a)?.len()<=2 || map.region_exits(b)?.len()<=2)
                && map.contracted_weight(&boundary,c)?<=gamma {
                return Err(OracleError::NotGranular);
            }
        }
        let (graph,regions,nonempty,wraps)=collapsed(&map,work)?;
        let exterior=map.arc_region(map.end_incident_arcs(map.chain().start)?[1][1])?;
        let mut separator=vec![false;n]; let mut groups=Vec::new();
        partition(graph,regions.clone(),threshold(regions.len()),&mut separator,&mut groups,work)?;
        let mut membership=vec![None;n]; for (i,group) in groups.iter().enumerate() { for r in group { membership[r.0]=Some(i); } }
        let separator_regions=map.region_ids().filter(|r|separator[r.0]).collect();
        Ok(Self { map,gamma,separator,groups,membership,nonempty,wraps,exterior,separator_regions })
    }
    pub fn map(&self) -> &Submap<'a, C> { &self.map }
    /// Consume preprocessing while moving out the unchanged sparse map.
    pub fn into_map(self) -> Submap<'a, C> { self.map }
    pub fn gamma(&self) -> usize { self.gamma }
    fn scan<P:RayProbe<C>>(&self, probe:&P, regions:impl Iterator<Item=RegionId>, best:&mut Option<P::Hit>, work:&mut Work) -> Result<(),OracleError> {
        let boundary=Boundary::new(self.map.input(),self.map.chain())?;
        for r in regions { for &a in self.map.region_arcs(r)? {
            work.retained_visits += 1;
            if let Some((start,end,full))=self.map.arc_sites(a) {
                let endpoints=self.map.arc_endpoints(a).ok_or(OracleError::InconsistentIncidence)?;
                let sources=[self.map.chord_level(endpoints[0].0)?,self.map.chord_level(endpoints[1].0)?];
                // Zero arc weight does not mean empty geometry: cap-only wrap
                // faces still have closed physical endpoints that block a ray.
                for (index,site) in [start,end].into_iter().enumerate() {
                    let edge=match site {
                        Site::Edge { edge,.. } => *edge,
                        Site::Vertex { vertex,.. } if *vertex==self.map.chain().end => EdgeId(vertex.0-1),
                        Site::Vertex { vertex,.. } => EdgeId(vertex.0),
                    };
                    work.arc_edge_visits+=1;
                    if let Some(hit)=probe.edge_hit(self.map.input(),edge,work) {
                        work.predicates+=1;
                        if probe.compare_endpoint(self.map.input(),&hit,site,sources[index])==Ordering::Equal { keep::<C,P>(probe,best,hit,work); }
                    }
                }
                for run in boundary.runs(&Arc { start,end,full_circuit:full }) {
                    let (Some(first),Some(last))=(run.first_edge(),run.last_edge()) else { continue; };
                    for e in first.0.min(last.0)..=first.0.max(last.0) {
                        work.arc_edge_visits += 1;
                        let edge=EdgeId(e); let Some(hit)=probe.edge_hit(self.map.input(),edge,work) else { continue; };
                        let (low,high)=if run.side==Side::Left { (run.from,run.to) } else { (run.to,run.from) };
                        let mut valid=true;
                        if let Position::Edge { edge:e,.. }=low { if e==edge {
                            let index=if run.side==Side::Left { 0 } else { 1 };
                            work.predicates+=1;
                            valid &= probe.compare_endpoint(self.map.input(),&hit,[start,end][index],sources[index])!=Ordering::Less;
                        } }
                        if let Position::Edge { edge:e,.. }=high { if e==edge {
                            let index=if run.side==Side::Left { 1 } else { 0 };
                            work.predicates+=1;
                            valid &= probe.compare_endpoint(self.map.input(),&hit,[start,end][index],sources[index])!=Ordering::Greater;
                        } }
                        if valid { keep::<C,P>(probe,best,hit,work); }
                    }
                }
            } else {
                for e in self.map.chain().start.0..self.map.chain().end.0 {
                    work.arc_edge_visits += 1;
                    if let Some(hit)=probe.edge_hit(self.map.input(),EdgeId(e),work) { keep::<C,P>(probe,best,hit,work); }
                }
            }
        } }
        Ok(())
    }
    fn hit_regions<P:RayProbe<C>>(&self,probe:&P,hit:&P::Hit,work:&mut Work)->Result<Vec<RegionId>,OracleError> {
        let boundary=Boundary::new(self.map.input(),self.map.chain())?; let edge=probe.edge(hit);
        work.predicates+=2;
        let vertex=if probe.parameter_cmp(hit,&C::Scalar::zero_value())==Ordering::Equal { Some(VertexId(edge.0)) } else if probe.parameter_cmp(hit,&C::Scalar::one_value())==Ordering::Equal { Some(VertexId(edge.0+1)) } else { None };
        let mut result=Vec::with_capacity(4);
        if let Some(vertex)=vertex {
            for side in [Side::Left,Side::Right] { for slot in if boundary.is_extremum(vertex) { &[Slot::Incoming,Slot::Outgoing][..] } else { &[Slot::Single][..] } {
                let site=Site::Vertex { vertex,side,slot:*slot };
                work.predicates+=1;
                if boundary.inside_null_pair(&site)? || !boundary.contact_faces_ray(&site,probe.direction())? { continue; }
                result.extend(incidence(&self.map,&boundary,&site,work)?);
            } }
        } else {
            let left=(probe.direction()==Direction::Right)==(self.map.input().edge_y_sign(edge)==Ordering::Greater);
            let side=if left { Side::Left } else { Side::Right };
            let arcs=self.map.canonical_arcs();
            if self.map.arc_sites(arcs[0]).is_none() { result.push(self.map.arc_region(arcs[0])?); }
            else {
                // Arc start identities retain the owning chord source. The
                // probe can move its threshold without rebuilding this order.
                let cmp=|arc,work:&mut Work| {
                    let site=self.map.arc_sites(arc).unwrap().0;
                    let (chord,_)=self.map.arc_endpoints(arc).unwrap()[0];
                    work.predicates+=1;
                    if site.side()!=side { if site.side()==Side::Left { Ordering::Less } else { Ordering::Greater } } else {
                        let physical=match site {
                            Site::Vertex { vertex,.. } => if vertex.0<=edge.0 { Ordering::Less } else { Ordering::Greater },
                            Site::Edge { edge:e,.. } => e.cmp(&edge).then_with(||probe.compare_endpoint(self.map.input(),hit,site,self.map.chord_level(chord).unwrap()).reverse()),
                        };
                        if side==Side::Right { physical.reverse() } else { physical }
                    }
                };
                let i=arcs.partition_point(|a|cmp(*a,work)!=Ordering::Greater);
                let j=if i==0 { arcs.len()-1 } else { i-1 }; let a=arcs[j];
                result.push(self.map.arc_region(a)?);
                if cmp(a,work)==Ordering::Equal { result.push(self.map.arc_region(arcs[(j+arcs.len()-1)%arcs.len()])?); }
            }
        }
        result.sort_by_key(|r|r.0); result.dedup(); result.retain(|r|self.nonempty[r.0]);
        if result.is_empty() { return Err(OracleError::InconsistentIncidence); } Ok(result)
    }
    fn right_regions<P:RayProbe<C>>(&self,probe:&P,work:&mut Work)->Vec<RegionId> {
        let i=self.wraps.partition_point(|w| { work.predicates+=1; probe.compare_source_level(self.map.input(),&w.source)==Ordering::Greater });
        if i<self.wraps.len() { work.predicates+=1; if probe.compare_source_level(self.map.input(),&self.wraps[i].source)==Ordering::Equal { return vec![self.wraps[i].lower,self.wraps[i].upper]; } }
        vec![if i==0 { self.wraps.first().map_or(self.exterior,|w|w.lower) } else { self.wraps[i-1].upper }]
    }
    pub fn shoot<P:RayProbe<C>>(&self,probe:&P,work:&mut Work)->Result<Option<P::Hit>,OracleError> {
        work.oracle_calls+=1;
        let mut best=None;
        self.scan(probe,self.separator_regions.iter().copied(),&mut best,work)?;
        let candidates=if let Some(hit)=&best { self.hit_regions(probe,hit,work)? } else { self.right_regions(probe,work) };
        if candidates.iter().any(|r|self.separator[r.0]) { return Ok(best); }
        let mut group=None;
        for r in candidates { if !self.nonempty[r.0] { continue; } let g=self.membership[r.0].ok_or(OracleError::InconsistentIncidence)?; if group.is_some_and(|i|i!=g) { return Err(OracleError::InconsistentIncidence); } group=Some(g); }
        let g=group.ok_or(OracleError::InconsistentIncidence)?;
        self.scan(probe,self.groups[g].iter().copied(),&mut best,work)?;
        Ok(best)
    }
}
fn keep<C:Curve,P:RayProbe<C>>(probe:&P,best:&mut Option<P::Hit>,hit:P::Hit,work:&mut Work) {
    let replace=match best { None=>true,Some(old)=> { work.predicates+=1; probe.compare_hits(&hit,old)==Ordering::Less } };
    if replace { *best=Some(hit); }
}

#[cfg(test)]
mod tests {
    use num_traits::{One, Zero};
    use super::*;
    use crate::boundary::Chain;
    use crate::geometry::Point;
    #[test]
    fn integer_separator_threshold_is_exact() {
        for n in 1..1000usize { let t=threshold(n); assert!((t as u128).pow(3)>=(n as u128).pow(2)); if t>1 { assert!(((t-1) as u128).pow(3)<(n as u128).pow(2)); } }
    }
    #[test]
    fn full_circle_source_is_a_geometric_blocker() {
        let input=Input::open(&[Point::integer(0,0),Point::integer(4,3)]).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(1)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap(); let mut work=Work::default();
        let map=Submap::from_verified_chords(&boundary,vec![],&mut work).unwrap();
        let oracle=RayOracle::build(map,2,&mut work).unwrap();
        let p=input.vertex(VertexId(0));
        let probe=PointProbe { x:p.x.clone(),y:p.y.clone(),direction:Direction::Right };
        let hit=oracle.shoot(&probe,&mut work).unwrap().unwrap();
        assert_eq!(hit.t,Rational::zero()); assert_eq!(hit.x,p.x);
    }
    #[test]
    fn rejects_hidden_long_uncut_arc() {
        let input=Input::open(&[Point::integer(0,0),Point::integer(2,3),Point::integer(4,1)]).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(input.len()-1)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap(); let mut work=Work::default();
        let map=Submap::from_verified_chords(&boundary,vec![],&mut work).unwrap();
        assert!(matches!(RayOracle::build(map,1,&mut work),Err(OracleError::NotGranular)));
    }
    #[test]
    fn zero_weight_wrap_face_is_not_contracted() {
        let input=Input::open(&[Point::integer(0,0),Point::integer(4,3)]).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(input.len()-1)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap(); let mut work=Work::default();
        let endpoints=[Side::Left,Side::Right].map(|side|Site::Vertex { vertex:chain.start,side,slot:Slot::Single });
        let mut map=Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord::certified(boundary,endpoints,Route::Wrap).unwrap()],&mut work).unwrap();
        let (_,_,nonempty,wraps)=collapsed(&map,&mut work).unwrap();
        assert_eq!(nonempty.iter().filter(|&&v|v).count(),2);
        assert_eq!(wraps.len(),1);
        // Granularity may subsequently remove this redundant chord; collapse
        // itself must preserve its positive-area, zero-arc-weight face.
        map.coarsen(&boundary,2*chain.edge_count(),&mut work).unwrap();
        let oracle=RayOracle::build(map,2*chain.edge_count(),&mut work).unwrap();
        let p=input.vertex(chain.start);
        for direction in [Direction::Left,Direction::Right] {
            let probe=PointProbe { x:p.x.clone(),y:p.y.clone(),direction };
            assert_eq!(oracle.shoot(&probe,&mut work).unwrap().unwrap().x,p.x);
        }
    }
    #[test]
    fn separator_and_residual_scans_match_exact_first_blocker() {
        let points:Vec<_>=(0i64..=64).map(|i|Point::integer(i-32,32-(i-32).abs())).collect();
        let input=Input::open(&points).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(input.len()-1)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap(); let mut work=Work::default();
        let apex=(0..input.len()).map(|i|input.vertex(VertexId(i)).y.clone()).max().unwrap();
        let base=input.vertex(chain.start).y.clone().max(input.vertex(chain.end).y.clone());
        let anchor=boundary.occurrences().next().unwrap();
        let whole=boundary.arc(&anchor,&anchor,true).unwrap();
        let mut chords:Vec<crate::submap::VisibleChord>=Vec::new();
        for source in boundary.occurrences() {
            let (target,route)=if boundary.inside_null_pair(&source).unwrap() {
                (boundary.companion(&source).unwrap().unwrap(),Route::Null)
            } else {
                let direction=boundary.direction(&source).unwrap();
                let mut nearest=boundary.nearest_contacts(&whole,&source,direction).unwrap().unwrap();
                let route=nearest.route;
                let target=nearest.find(|hit| {
                    boundary.direction(&hit.site).unwrap()!=direction
                        && !boundary.inside_null_pair(&hit.site).unwrap()
                }).unwrap().site;
                (target,route)
            };
            if !chords.iter().any(|chord|chord.endpoints.contains(&source)) {
                chords.push(crate::submap::VisibleChord::certified(boundary,[source,target],route).unwrap());
            }
        }
        let mut map=Submap::from_verified_chords(&boundary,chords,&mut work).unwrap();
        map.coarsen(&boundary,8,&mut work).unwrap();
        let oracle=RayOracle::build(map,8,&mut work).unwrap();
        assert!(!oracle.separator_regions.is_empty());
        assert!(oracle.groups.iter().all(|g|g.len()<=threshold(10)));
        let mut with_separator=false;
        for j in 1..20 {
            let y=&base+(&apex-&base)*Rational::new(j.into(),20.into());
            for direction in [Direction::Left,Direction::Right] {
                let probe=PointProbe { x:Rational::zero(),y:y.clone(),direction };
                let mut separator_hit=None;
                oracle.scan(&probe,oracle.separator_regions.iter().copied(),&mut separator_hit,&mut work).unwrap();
                with_separator|=separator_hit.is_some();
                let mut expected=None;
                for e in chain.start.0..chain.end.0 { if let Some(hit)=probe.edge_hit(&input,EdgeId(e),&mut work) { keep::<Input,_>(&probe,&mut expected,hit,&mut work); } }
                let before=work.arc_edge_visits;
                let actual=oracle.shoot(&probe,&mut work).unwrap();
                assert_eq!(actual.as_ref().map(|h|&h.x),expected.as_ref().map(|h|&h.x));
                let scanned=oracle.separator_regions.len()+threshold(10);
                assert!(work.arc_edge_visits-before<=((8*chain.edge_count()+8)*scanned) as u128);
            }
        }
        assert!(with_separator);
        let probe=PointProbe { x:Rational::zero(),y:apex+Rational::one(),direction:Direction::Right };
        assert!(oracle.shoot(&probe,&mut work).unwrap().is_none());
        let mut separator_hit=None;
        oracle.scan(&probe,oracle.separator_regions.iter().copied(),&mut separator_hit,&mut work).unwrap();
        assert!(separator_hit.is_none());
    }
    #[test]
    fn intrinsic_null_face_disappears_but_vertex_hit_ties_remain() {
        let input=Input::open(&[Point::integer(-3,0),Point::integer(0,4),Point::integer(3,0)]).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(input.len()-1)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap(); let vertex=VertexId(1);
        assert!(boundary.is_extremum(vertex));
        let mut work=Work::default();
        let site=[Side::Left,Side::Right].into_iter().map(|side|Site::Vertex { vertex,side,slot:Slot::Incoming })
            .find(|s|boundary.inside_null_pair(s).unwrap()).unwrap();
        let companion=boundary.companion(&site).unwrap().unwrap();
        let map=Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord::certified(boundary,[site,companion],Route::Null).unwrap()],&mut work).unwrap();
        let (_,_,nonempty,wraps)=collapsed(&map,&mut work).unwrap();
        assert_eq!(nonempty.iter().filter(|&&v|v).count(),1); assert!(wraps.is_empty());
        let p=input.vertex(vertex);
        let probe=PointProbe { x:p.x.clone(),y:p.y.clone(),direction:Direction::Right };
        let a=probe.edge_hit(&input,EdgeId(0),&mut work).unwrap();
        let b=probe.edge_hit(&input,EdgeId(1),&mut work).unwrap();
        assert_eq!(<PointProbe as RayProbe<Input>>::compare_hits(&probe,&a,&b),Ordering::Equal);
        assert_eq!(<PointProbe as RayProbe<Input>>::parameter_cmp(&probe,&a,&Rational::one()),Ordering::Equal);
        assert_eq!(<PointProbe as RayProbe<Input>>::parameter_cmp(&probe,&b,&Rational::zero()),Ordering::Equal);
    }

    type Sym = crate::symbolic::Symbolic<'static>;
    fn sym(n: usize) -> Sym { Sym::from_usize_value(n) }
    fn fraction(n: usize,d: usize) -> Sym { sym(n).over(&sym(d)) }

    // A genuinely bent exact curve, deliberately not Clone. Its optional
    // projective chart has two interior input-cut events, neither a chord.
    struct BentCurve {
        vertices: [Point<Sym>;3],
        projective: bool,
        cuts: Vec<crate::curve::CutCrossing<Sym>>,
        tangent_calls: std::cell::Cell<usize>,
        interior_tangent_calls: std::cell::Cell<usize>,
    }
    impl BentCurve {
        fn new(projective: bool) -> Self {
            let mut curve=Self { vertices:[Point::new(sym(0),sym(0)),Point::new(sym(2),sym(3)),Point::new(sym(4),sym(1))],
                projective,cuts:Vec::new(),tangent_calls:std::cell::Cell::new(0),interior_tangent_calls:std::cell::Cell::new(0) };
            if projective {
                curve.cuts=vec![
                    crate::curve::CutCrossing { edge:EdgeId(0),parameter:fraction(2,3),level:LevelSource::frozen(sym(2)),forward:Ordering::Less },
                    crate::curve::CutCrossing { edge:EdgeId(1),parameter:fraction(1,4),level:LevelSource::frozen(fraction(5,2)),forward:Ordering::Greater },
                ];
            }
            curve
        }
        fn raw(&self,edge:EdgeId,t:&Sym) -> (Point<Sym>,Point<Sym>) {
            let a=&self.vertices[edge.0]; let b=&self.vertices[edge.0+1];
            let dy=b.y.minus(&a.y); let dx=b.x.minus(&a.x);
            let bubble=t.times(&sym(1).minus(t));
            let derivative=sym(1).minus(&sym(2).times(t));
            let (bump,slope)=if self.projective {
                let cut=if edge.0==0 { fraction(2,3) } else { fraction(1,4) };
                (bubble.times(&t.minus(&cut)),derivative.times(&t.minus(&cut)).plus(&bubble))
            } else { (bubble,derivative) };
            let epsilon=Sym::variable(0);
            (Point::new(a.x.plus(&t.times(&dx)).plus(&epsilon.times(&bump)),a.y.plus(&t.times(&dy))),
                Point::new(dx.plus(&epsilon.times(&slope)),dy))
        }
        fn denominator(point:&Point<Sym>) -> Sym { sym(7).times(&point.y).minus(&sym(10)).over(&sym(3)).minus(&point.x) }
    }
    impl Curve for BentCurve {
        type Scalar=Sym;
        const MAX_LEAF_EDGES: usize=16;
        fn len(&self)->usize { 3 }
        fn vertex(&self,vertex:VertexId)->std::borrow::Cow<'_,Point<Sym>> {
            if self.projective {
                let p=&self.vertices[vertex.0];
                std::borrow::Cow::Owned(Point::new(sym(1).over(&Self::denominator(p)),p.y.clone()))
            } else { std::borrow::Cow::Borrowed(&self.vertices[vertex.0]) }
        }
        fn edge_y_sign(&self,edge:EdgeId)->Ordering { self.vertices[edge.0+1].y.cmp(&self.vertices[edge.0].y) }
        fn turn(&self,vertex:VertexId)->Ordering {
            let a=self.edge_tangent(EdgeId(vertex.0-1),&sym(1));
            let b=self.edge_tangent(EdgeId(vertex.0),&sym(0));
            a.x.times(&b.y).minus(&a.y.times(&b.x)).sign()
        }
        fn horizontal_hit(&self,edge:EdgeId,level:&Sym)->Option<(Sym,Sym)> {
            let a=&self.vertices[edge.0]; let b=&self.vertices[edge.0+1];
            if level<std::cmp::min(&a.y,&b.y) || level>std::cmp::max(&a.y,&b.y) { return None; }
            let t=level.minus(&a.y).over(&b.y.minus(&a.y));
            let (p,_)=self.raw(edge,&t);
            if self.projective && Self::denominator(&p).is_zero_value() { return None; }
            Some((t,self.edge_point(edge,&level.minus(&a.y).over(&b.y.minus(&a.y))).x))
        }
        fn edge_point(&self,edge:EdgeId,t:&Sym)->Point<Sym> {
            let (p,_)=self.raw(edge,t);
            if self.projective { Point::new(sym(1).over(&Self::denominator(&p)),p.y) } else { p }
        }
        fn edge_tangent(&self,edge:EdgeId,t:&Sym)->Point<Sym> {
            self.tangent_calls.set(self.tangent_calls.get()+1);
            if t.sign()==Ordering::Greater && t.compare_one()==Ordering::Less {
                self.interior_tangent_calls.set(self.interior_tangent_calls.get()+1);
            }
            let (p,d)=self.raw(edge,t);
            if self.projective {
                let denominator=Self::denominator(&p);
                Point::new(d.x.minus(&fraction(7,3).times(&d.y)).over(&denominator.times(&denominator)),d.y)
            } else { d }
        }
        fn cut_crossings(&self)->&[crate::curve::CutCrossing<Sym>] { &self.cuts }
    }
    fn arch_map<'a,C:Curve>(curve:&'a C,work:&mut Work)->Submap<'a,C> {
        let chain=Chain::new(curve,VertexId(0),VertexId(2)).unwrap();
        let boundary=Boundary::new(curve,chain).unwrap();
        let (t,_)=curve.horizontal_hit(EdgeId(0),&curve.vertex(VertexId(2)).y).unwrap();
        let endpoints=[Site::Vertex { vertex:VertexId(2),side:Side::Right,slot:Slot::Single },
            Site::Edge { edge:EdgeId(0),t,side:Side::Right }];
        Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord::certified(boundary,endpoints,Route::Finite).unwrap()],work).unwrap()
    }
    #[test]
    fn nonclone_symbolic_curves_use_actual_tangents_and_first_blockers() {
        let curve=BentCurve::new(false); let mut work=Work::default();
        let oracle=RayOracle::build(arch_map(&curve,&mut work),3,&mut work).unwrap();
        let _snapshot=oracle.clone();
        assert!(curve.tangent_calls.get()>=4);
        assert!(curve.interior_tangent_calls.get()>0,"retained augmented contacts need their actual tangent germs");
        assert_ne!(curve.edge_tangent(EdgeId(0),&sym(0)).x,sym(2));
        for y in [sym(0),fraction(1,2),sym(1),sym(2),sym(3),sym(4)] {
            for direction in [Direction::Left,Direction::Right] {
                let probe=PointProbe { x:sym(1),y:y.clone(),direction };
                let mut expected=None;
                for e in 0..2 { if let Some(hit)=probe.edge_hit(&curve,EdgeId(e),&mut work) { keep::<BentCurve,_>(&probe,&mut expected,hit,&mut work); } }
                assert_eq!(oracle.shoot(&probe,&mut work).unwrap(),expected);
            }
        }
        let probe=PointProbe { x:sym(0),y:sym(4),direction:Direction::Right };
        let before=work.predicates;
        assert!(probe.edge_hit(&curve,EdgeId(0),&mut work).is_none());
        assert_eq!(work.predicates,before+1);
    }

    struct DisplacedProbe<'a> { point:PointProbe,view:&'a Input }
    impl RayProbe for DisplacedProbe<'_> {
        type Hit=PointHit;
        fn edge_hit(&self,_:&Input,edge:EdgeId,work:&mut Work)->Option<PointHit> { self.point.edge_hit(self.view,edge,work) }
        fn edge(&self,hit:&PointHit)->EdgeId { hit.edge }
        fn parameter_cmp(&self,hit:&PointHit,t:&Rational)->Ordering { hit.t.cmp(t) }
        fn compare_hits(&self,a:&PointHit,b:&PointHit)->Ordering { ray_order(&self.point.x,self.point.direction,&a.x,&b.x) }
        fn compare_level(&self,y:&Rational)->Ordering { self.point.y.cmp(y) }
        fn direction(&self)->Direction { self.point.direction }
        fn compare_endpoint(&self,_:&Input,hit:&PointHit,endpoint:&Site,source:&LevelSource)->Ordering {
            match endpoint {
                Site::Edge { edge,.. } => {
                    let (threshold,_)=self.view.horizontal_hit(*edge,self.view.level(source).as_ref()).unwrap();
                    hit.t.cmp(&threshold)
                }
                Site::Vertex { vertex,.. } => hit.t.cmp(&if vertex.0==hit.edge.0 { Rational::zero() } else { Rational::one() }),
            }
        }
        fn compare_source_level(&self,_:&Input,source:&LevelSource)->Ordering { self.point.y.cmp(self.view.level(source).as_ref()) }
    }
    #[test]
    fn saved_augmented_endpoint_clipping_and_incidence_reevaluate_source() {
        // Keep the normalization identical in both inputs: the unchanged
        // half-integer levels give both charts the same denominator bound.
        let points=[Point::new(Rational::zero(),Rational::new(1.into(),2.into())),
            Point::new(Rational::from_integer(2.into()),Rational::new(7.into(),2.into())),
            Point::new(Rational::from_integer(4.into()),Rational::new(3.into(),2.into()))];
        let input=Input::open(&points).unwrap();
        let mut shifted=points;
        shifted[2].y=Rational::from_integer(2.into());
        let view=Input::open(&shifted).unwrap();
        let mut work=Work::default();
        let oracle=RayOracle::build(arch_map(&input,&mut work),3,&mut work).unwrap();
        let boundary=Boundary::new(&input,oracle.map.chain()).unwrap();
        let threshold=input.horizontal_hit(EdgeId(0),&input.vertex(VertexId(2)).y).unwrap().0;
        let below=Site::Edge { edge:EdgeId(0),t:&threshold/Rational::from_integer(2.into()),side:Side::Right };
        let above=Site::Edge { edge:EdgeId(0),t:(&threshold+Rational::one())/Rational::from_integer(2.into()),side:Side::Right };
        let exterior=incidence(&oracle.map,&boundary,&below,&mut work).unwrap()[1];
        let interior=incidence(&oracle.map,&boundary,&above,&mut work).unwrap()[1];
        assert_ne!(exterior,interior);
        let middle=(&input.vertex(VertexId(2)).y+&view.vertex(VertexId(2)).y)/Rational::from_integer(2.into());
        let probe=DisplacedProbe { view:&view,point:PointProbe { x:Rational::from_integer(2.into()),y:middle,direction:Direction::Left } };
        let hit=probe.edge_hit(&input,EdgeId(0),&mut work).unwrap();
        assert_eq!(oracle.hit_regions(&probe,&hit,&mut work).unwrap(),vec![exterior]);
        assert_eq!(oracle.hit_regions(&probe.point,&hit,&mut work).unwrap(),vec![interior]);
        let mut clipped=None;
        oracle.scan(&probe,std::iter::once(interior),&mut clipped,&mut work).unwrap();
        assert!(clipped.is_none(),"the old endpoint threshold must not admit a hit below its moved source");
        assert_eq!(oracle.shoot(&probe,&mut work).unwrap(),Some(hit));
        let contact=DisplacedProbe { view:&view,point:PointProbe { x:Rational::from_integer(2.into()),y:view.vertex(VertexId(2)).y.clone(),direction:Direction::Left } };
        let hit=contact.edge_hit(&input,EdgeId(0),&mut work).unwrap();
        assert_eq!(oracle.hit_regions(&contact,&hit,&mut work).unwrap().len(),2);
    }
    #[test]
    fn saved_wrap_lookup_keeps_displaced_vertex_level_source() {
        let points=[Point::new(Rational::zero(),Rational::new(1.into(),2.into())),
            Point::new(Rational::from_integer(2.into()),Rational::new(7.into(),2.into())),
            Point::new(Rational::from_integer(4.into()),Rational::new(3.into(),2.into()))];
        let input=Input::open(&points).unwrap();
        let mut shifted=points;
        shifted[2].y=Rational::from_integer(2.into());
        let view=Input::open(&shifted).unwrap();
        let chain=Chain::new(&input,VertexId(0),VertexId(2)).unwrap();
        let boundary=Boundary::new(&input,chain).unwrap();
        let endpoints=[Site::Vertex { vertex:VertexId(2),side:Side::Left,slot:Slot::Single },
            Site::Edge { edge:EdgeId(0),t:input.horizontal_hit(EdgeId(0),&input.vertex(VertexId(2)).y).unwrap().0,side:Side::Left }];
        let mut work=Work::default();
        let map=Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord::certified(boundary,endpoints,Route::Wrap).unwrap()],&mut work).unwrap();
        let oracle=RayOracle::build(map,3,&mut work).unwrap();
        assert!(matches!(oracle.wraps[0].source,LevelSource::Vertex(VertexId(2))));
        let middle=(&input.vertex(VertexId(2)).y+&view.vertex(VertexId(2)).y)/Rational::from_integer(2.into());
        let probe=DisplacedProbe { view:&view,point:PointProbe { x:Rational::zero(),y:middle,direction:Direction::Right } };
        assert_eq!(oracle.right_regions(&probe,&mut work),vec![oracle.wraps[0].lower]);
        assert_eq!(oracle.right_regions(&probe.point,&mut work),vec![oracle.wraps[0].upper]);
    }
    #[test]
    fn input_chart_cuts_select_far_right_faces_without_wrapping_chords() {
        let curve=BentCurve::new(true); let mut work=Work::default();
        let oracle=RayOracle::build(arch_map(&curve,&mut work),3,&mut work).unwrap();
        assert!(oracle.map.chord_ids().all(|c|oracle.map.chord(c).unwrap().1==Route::Finite));
        assert_eq!(oracle.wraps.len(),2);
        assert!(oracle.separator_regions.is_empty());
        let boundary=Boundary::new(&curve,oracle.map.chain()).unwrap();
        let left=Site::Edge { edge:EdgeId(0),t:fraction(3,4),side:Side::Left };
        let right=Site::Edge { edge:EdgeId(0),t:fraction(3,4),side:Side::Right };
        let exterior=incidence(&oracle.map,&boundary,&left,&mut work).unwrap()[1];
        let interior=incidence(&oracle.map,&boundary,&right,&mut work).unwrap()[1];
        assert_ne!(exterior,interior);
        for (y,region) in [(fraction(3,2),exterior),(fraction(9,4),interior),(fraction(11,4),exterior)] {
            let probe=PointProbe { x:sym(0),y,direction:Direction::Right };
            assert_eq!(oracle.right_regions(&probe,&mut work),vec![region]);
            let mut separator_hit=None;
            oracle.scan(&probe,oracle.separator_regions.iter().copied(),&mut separator_hit,&mut work).unwrap();
            assert!(separator_hit.is_none());
            let mut expected=None;
            for e in 0..2 { if let Some(hit)=probe.edge_hit(&curve,EdgeId(e),&mut work) { keep::<BentCurve,_>(&probe,&mut expected,hit,&mut work); } }
            assert_eq!(oracle.shoot(&probe,&mut work).unwrap(),expected);
        }
    }
}
