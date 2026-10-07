//! Separator ray shooting on the collapsed spherical subdivision (§3.4).
//! Preprocessing touches retained records only; queries scan original arc pieces.
//! The owned map must be compact, conformal and gamma-granular. Collapsed
//! degree-two curve bends stay implicit, whereas nonnull wrapping loops stay
//! explicit even when their faces have zero boundary-arc weight. Construction
//! costs O(mu log m); separator and residual scans cost
//! O(gamma * ceil(mu^(2/3)) + log m) geometric operations per query.
use std::cmp::Ordering;
use std::fmt;
use num_traits::{One, Zero};
use crate::boundary::{Arc, Boundary, BoundaryError, Position, Side, Site, Slot};
use crate::geometry::{Direction, Rational, Route, horizontal_hit, ray_order};
use crate::input::{EdgeId, Input, VertexId};
use crate::separator::{Dart, EmbeddedGraph, Separator, SeparatorError};
use crate::submap::{MapError, RegionId, Submap};
use crate::work::Work;

pub trait RayProbe {
    type Hit: Clone;
    fn edge_hit(&self, input: &Input, edge: EdgeId, work: &mut Work) -> Option<Self::Hit>;
    fn edge(&self, hit: &Self::Hit) -> EdgeId;
    fn parameter_cmp(&self, hit: &Self::Hit, t: &Rational) -> Ordering;
    fn compare_hits(&self, a: &Self::Hit, b: &Self::Hit) -> Ordering;
    fn compare_level(&self, y: &Rational) -> Ordering;
    fn direction(&self) -> Direction;
}

#[derive(Clone, Debug)]
pub struct RationalProbe { pub x: Rational, pub y: Rational, pub direction: Direction }
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RationalHit { pub edge: EdgeId, pub t: Rational, pub x: Rational }
impl RayProbe for RationalProbe {
    type Hit = RationalHit;
    fn edge_hit(&self, input: &Input, edge: EdgeId, work: &mut Work) -> Option<RationalHit> {
        work.predicates += 1;
        let (t, x) = horizontal_hit(input.vertex(VertexId(edge.0)), input.vertex(VertexId(edge.0 + 1)), &self.y)?;
        Some(RationalHit { edge, t, x })
    }
    fn edge(&self, hit: &RationalHit) -> EdgeId { hit.edge }
    fn parameter_cmp(&self, hit: &RationalHit, t: &Rational) -> Ordering { hit.t.cmp(t) }
    fn compare_hits(&self, a: &RationalHit, b: &RationalHit) -> Ordering { ray_order(&self.x, self.direction, &a.x, &b.x) }
    fn compare_level(&self, y: &Rational) -> Ordering { self.y.cmp(y) }
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
struct Place { edge: usize, t: Rational }
impl Place {
    fn site(site: &Site) -> Self { match site {
        Site::Vertex { vertex, .. } => Self { edge: vertex.0, t: Rational::zero() },
        Site::Edge { edge, t, .. } => Self { edge: edge.0, t: t.clone() },
    } }
}
#[derive(Clone, Debug)]
struct WrapLevel { y: Rational, lower: RegionId, upper: RegionId }
#[derive(Clone, Debug)]
pub struct RayOracle<'a> {
    map: Submap<'a>, gamma: usize, separator: Vec<bool>, groups: Vec<Vec<RegionId>>,
    membership: Vec<Option<usize>>, nonempty: Vec<bool>, wraps: Vec<WrapLevel>, exterior: RegionId,
    separator_regions: Vec<RegionId>,
}

fn incidence(map: &Submap<'_>, boundary: &Boundary<'_>, site: &Site, work: &mut Work) -> Result<[RegionId; 2], OracleError> {
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
fn angle(a: &(Rational, Rational), b: &(Rational, Rational)) -> Ordering {
    let half = |v: &(Rational, Rational)| v.1 > Rational::zero() || (v.1.is_zero() && v.0 > Rational::zero());
    half(b).cmp(&half(a)).then_with(|| (&a.0 * &b.1 - &a.1 * &b.0).cmp(&Rational::zero()).reverse())
}
fn add_edge(rotations: &mut [Vec<usize>], ends: &mut Vec<usize>, labels: &mut Vec<RegionId>, tangents: &mut Vec<(Rational, Rational)>, a: usize, b: usize, left: RegionId, right: RegionId, ta: (Rational, Rational), tb: (Rational, Rational)) {
    let d = ends.len(); ends.extend([a,b]); labels.extend([left,right]); tangents.extend([ta,tb]);
    rotations[a].push(d); rotations[b].push(d+1);
}
fn collapsed(map: &Submap<'_>, work: &mut Work) -> Result<(EmbeddedGraph, Vec<RegionId>, Vec<bool>, Vec<WrapLevel>), OracleError> {
    let boundary = Boundary::new(map.input(), map.chain())?;
    let mut places = vec![Place { edge: map.chain().start.0, t: Rational::zero() }, Place { edge: map.chain().end.0, t: Rational::zero() }];
    for c in map.chord_ids() { work.retained_visits += 1; let (s, _) = map.chord(c)?; places.extend(s.into_iter().map(Place::site)); }
    places.sort_unstable_by(|a,b| { work.predicates+=1; a.cmp(b) });
    places.dedup_by(|a,b| { work.predicates+=1; a==b });
    let mut rotations = vec![Vec::new(); places.len()];
    let mut ends = Vec::new(); let mut labels = Vec::new(); let mut tangents = Vec::new();
    for i in 0..places.len()-1 {
        work.retained_visits += 1;
        let p = &places[i]; let q = &places[i+1];
        // A sample immediately after p suffices: no retained endpoint lies
        // inside this bent interval, even when it spans many input edges.
        let t = if p.edge == q.edge { (&p.t + &q.t) / Rational::from_integer(2.into()) } else { (&p.t + Rational::one()) / Rational::from_integer(2.into()) };
        let sample = Site::Edge { edge: EdgeId(p.edge), t, side: Side::Left };
        let l = incidence(map, &boundary, &sample, work)?[1];
        let sample = match sample { Site::Edge { edge, t, .. } => Site::Edge { edge, t, side: Side::Right }, _ => unreachable!() };
        let r = incidence(map, &boundary, &sample, work)?[1];
        let a = map.input().vertex(VertexId(p.edge)); let b = map.input().vertex(VertexId(p.edge+1));
        let previous = if q.t.is_zero() { q.edge-1 } else { q.edge };
        let c = map.input().vertex(VertexId(previous)); let d = map.input().vertex(VertexId(previous+1));
        add_edge(&mut rotations, &mut ends, &mut labels, &mut tangents, i, i+1, l, r, (&b.x-&a.x,&b.y-&a.y), (&c.x-&d.x,&c.y-&d.y));
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
                    if place.t.is_zero() { Ordering::Equal } else { Ordering::Greater }
                }),
                Site::Edge { edge, t, .. } => place.edge.cmp(&edge.0).then_with(|| place.t.cmp(t)),
            }
        }).unwrap());
        let regions = map.chord_regions(c)?; let direction = boundary.direction(s[0])?;
        let dx = if direction == Direction::Right { Rational::one() } else { -Rational::one() };
        add_edge(&mut rotations, &mut ends, &mut labels, &mut tangents, a,b,regions[1],regions[0],(dx.clone(),Rational::zero()),(-dx,Rational::zero()));
        if route == Route::Wrap {
            let (lower,upper) = if direction == Direction::Right { (regions[0],regions[1]) } else { (regions[1],regions[0]) };
            wraps.push(WrapLevel { y: boundary.point(s[0])?.y, lower, upper });
        }
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
    wraps.sort_by(|a,b| { work.predicates+=1; a.y.cmp(&b.y) });
    for pair in wraps.windows(2) {
        work.predicates += 1;
        if pair[0].y == pair[1].y || pair[0].upper != pair[1].lower { return Err(OracleError::InconsistentIncidence); }
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

impl<'a> RayOracle<'a> {
    pub fn build(map: Submap<'a>, gamma: usize, work: &mut Work) -> Result<Self,OracleError> {
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
    pub fn map(&self) -> &Submap<'a> { &self.map }
    pub fn gamma(&self) -> usize { self.gamma }
    fn scan<P:RayProbe>(&self, probe:&P, regions:impl Iterator<Item=RegionId>, best:&mut Option<P::Hit>, work:&mut Work) -> Result<(),OracleError> {
        let boundary=Boundary::new(self.map.input(),self.map.chain())?;
        for r in regions { for &a in self.map.region_arcs(r)? {
            work.retained_visits += 1;
            if let Some((start,end,full))=self.map.arc_sites(a) {
                // Zero arc weight does not mean empty geometry: cap-only wrap
                // faces still have closed physical endpoints that block a ray.
                for site in [start,end] {
                    let (edge,t)=match site {
                        Site::Edge { edge,t,.. } => (*edge,t.clone()),
                        Site::Vertex { vertex,.. } if *vertex==self.map.chain().end => (EdgeId(vertex.0-1),Rational::one()),
                        Site::Vertex { vertex,.. } => (EdgeId(vertex.0),Rational::zero()),
                    };
                    work.arc_edge_visits+=1;
                    if let Some(hit)=probe.edge_hit(self.map.input(),edge,work) {
                        work.predicates+=1;
                        if probe.parameter_cmp(&hit,&t)==Ordering::Equal { keep(probe,best,hit,work); }
                    }
                }
                for run in boundary.runs(&Arc { start,end,full_circuit:full }) {
                    let (Some(first),Some(last))=(run.first_edge(),run.last_edge()) else { continue; };
                    for e in first.0.min(last.0)..=first.0.max(last.0) {
                        work.arc_edge_visits += 1;
                        let edge=EdgeId(e); let Some(hit)=probe.edge_hit(self.map.input(),edge,work) else { continue; };
                        let (low,high)=if run.side==Side::Left { (run.from,run.to) } else { (run.to,run.from) };
                        let mut valid=true;
                        if let Position::Edge { edge:e,t }=low { if e==edge { work.predicates+=1; valid &= probe.parameter_cmp(&hit,t)!=Ordering::Less; } }
                        if let Position::Edge { edge:e,t }=high { if e==edge { work.predicates+=1; valid &= probe.parameter_cmp(&hit,t)!=Ordering::Greater; } }
                        if valid { keep(probe,best,hit,work); }
                    }
                }
            } else {
                for e in self.map.chain().start.0..self.map.chain().end.0 {
                    work.arc_edge_visits += 1;
                    if let Some(hit)=probe.edge_hit(self.map.input(),EdgeId(e),work) { keep(probe,best,hit,work); }
                }
            }
        } }
        Ok(())
    }
    fn hit_regions<P:RayProbe>(&self,probe:&P,hit:&P::Hit,work:&mut Work)->Result<Vec<RegionId>,OracleError> {
        let boundary=Boundary::new(self.map.input(),self.map.chain())?; let edge=probe.edge(hit);
        work.predicates+=2;
        let vertex=if probe.parameter_cmp(hit,&Rational::zero())==Ordering::Equal { Some(VertexId(edge.0)) } else if probe.parameter_cmp(hit,&Rational::one())==Ordering::Equal { Some(VertexId(edge.0+1)) } else { None };
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
                // Compare symbolic parameters directly, without materializing a
                // rational intersection or an occurrence table.
                let cmp=|site:&Site,work:&mut Work| {
                    work.predicates+=1;
                    if site.side()!=side { if site.side()==Side::Left { Ordering::Less } else { Ordering::Greater } } else {
                        let physical=match site {
                            Site::Vertex { vertex,.. } => if vertex.0<=edge.0 { Ordering::Less } else { Ordering::Greater },
                            Site::Edge { edge:e,t,.. } => e.cmp(&edge).then_with(||probe.parameter_cmp(hit,t).reverse()),
                        };
                        if side==Side::Right { physical.reverse() } else { physical }
                    }
                };
                let i=arcs.partition_point(|a|cmp(self.map.arc_sites(*a).unwrap().0,work)!=Ordering::Greater);
                let j=if i==0 { arcs.len()-1 } else { i-1 }; let a=arcs[j];
                result.push(self.map.arc_region(a)?);
                if cmp(self.map.arc_sites(a).unwrap().0,work)==Ordering::Equal { result.push(self.map.arc_region(arcs[(j+arcs.len()-1)%arcs.len()])?); }
            }
        }
        result.sort_by_key(|r|r.0); result.dedup(); result.retain(|r|self.nonempty[r.0]);
        if result.is_empty() { return Err(OracleError::InconsistentIncidence); } Ok(result)
    }
    fn right_regions<P:RayProbe>(&self,probe:&P,work:&mut Work)->Vec<RegionId> {
        let i=self.wraps.partition_point(|w| { work.predicates+=1; probe.compare_level(&w.y)==Ordering::Greater });
        if i<self.wraps.len() { work.predicates+=1; if probe.compare_level(&self.wraps[i].y)==Ordering::Equal { return vec![self.wraps[i].lower,self.wraps[i].upper]; } }
        vec![if i==0 { self.wraps.first().map_or(self.exterior,|w|w.lower) } else { self.wraps[i-1].upper }]
    }
    pub fn shoot<P:RayProbe>(&self,probe:&P,work:&mut Work)->Result<Option<P::Hit>,OracleError> {
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
fn keep<P:RayProbe>(probe:&P,best:&mut Option<P::Hit>,hit:P::Hit,work:&mut Work) {
    let replace=match best { None=>true,Some(old)=> { work.predicates+=1; probe.compare_hits(&hit,old)==Ordering::Less } };
    if replace { *best=Some(hit); }
}

#[cfg(test)]
mod tests {
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
        let probe=RationalProbe { x:p.x.clone(),y:p.y.clone(),direction:Direction::Right };
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
        let mut map=Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord { endpoints,route:Route::Wrap }],&mut work).unwrap();
        let (_,_,nonempty,wraps)=collapsed(&map,&mut work).unwrap();
        assert_eq!(nonempty.iter().filter(|&&v|v).count(),2);
        assert_eq!(wraps.len(),1);
        // Granularity may subsequently remove this redundant chord; collapse
        // itself must preserve its positive-area, zero-arc-weight face.
        map.coarsen(&boundary,2*chain.edge_count(),&mut work).unwrap();
        let oracle=RayOracle::build(map,2*chain.edge_count(),&mut work).unwrap();
        let p=input.vertex(chain.start);
        for direction in [Direction::Left,Direction::Right] {
            let probe=RationalProbe { x:p.x.clone(),y:p.y.clone(),direction };
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
                chords.push(crate::submap::VisibleChord { endpoints:[source,target],route });
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
                let probe=RationalProbe { x:Rational::zero(),y:y.clone(),direction };
                let mut separator_hit=None;
                oracle.scan(&probe,oracle.separator_regions.iter().copied(),&mut separator_hit,&mut work).unwrap();
                with_separator|=separator_hit.is_some();
                let mut expected=None;
                for e in chain.start.0..chain.end.0 { if let Some(hit)=probe.edge_hit(&input,EdgeId(e),&mut work) { keep(&probe,&mut expected,hit,&mut work); } }
                let before=work.arc_edge_visits;
                let actual=oracle.shoot(&probe,&mut work).unwrap();
                assert_eq!(actual.as_ref().map(|h|&h.x),expected.as_ref().map(|h|&h.x));
                let scanned=oracle.separator_regions.len()+threshold(10);
                assert!(work.arc_edge_visits-before<=((8*chain.edge_count()+8)*scanned) as u128);
            }
        }
        assert!(with_separator);
        let probe=RationalProbe { x:Rational::zero(),y:apex+Rational::one(),direction:Direction::Right };
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
        let map=Submap::from_verified_chords(&boundary,vec![crate::submap::VisibleChord { endpoints:[site,companion],route:Route::Null }],&mut work).unwrap();
        let (_,_,nonempty,wraps)=collapsed(&map,&mut work).unwrap();
        assert_eq!(nonempty.iter().filter(|&&v|v).count(),1); assert!(wraps.is_empty());
        let p=input.vertex(vertex);
        let probe=RationalProbe { x:p.x.clone(),y:p.y.clone(),direction:Direction::Right };
        let a=probe.edge_hit(&input,EdgeId(0),&mut work).unwrap();
        let b=probe.edge_hit(&input,EdgeId(1),&mut work).unwrap();
        assert_eq!(probe.compare_hits(&a,&b),Ordering::Equal);
        assert_eq!(probe.parameter_cmp(&a,&Rational::one()),Ordering::Equal);
        assert_eq!(probe.parameter_cmp(&b,&Rational::zero()),Ordering::Equal);
    }
}
