/// Geometric-operation accounting, independent of exact-arithmetic bit costs.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct Work {
    pub predicates: u128,
    pub arc_edge_visits: u128,
    pub retained_visits: u128,
    pub oracle_calls: u128,
    pub fusion_events: u128,
    pub decomposition_visits: u128,
    pub separator_visits: u128,
}
