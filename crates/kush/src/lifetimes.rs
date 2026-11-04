//! Finite outlives constraints. Solving adds only paths already justified by
//! input edges; SCCs are equivalence classes, not permission to invent bounds.
use std::collections::{BTreeMap, BTreeSet, VecDeque};
type Bounds = BTreeSet<(String, String)>;

pub(crate) struct LifetimeGraph {
    edges: Bounds,
}
pub(crate) struct Solution {
    pub(crate) closure: Bounds,
    pub(crate) components: Vec<Vec<String>>,
}
impl LifetimeGraph {
    pub(crate) fn new(edges: &Bounds) -> Self {
        Self {
            edges: edges.clone(),
        }
    }
    pub(crate) fn solve(&self) -> Solution {
        let names: Vec<_> = self
            .edges
            .iter()
            .flat_map(|(a, b)| [a.clone(), b.clone()])
            .collect::<BTreeSet<_>>()
            .into_iter()
            .collect();
        let ids: BTreeMap<_, _> = names
            .iter()
            .enumerate()
            .map(|(i, n)| (n.as_str(), i))
            .collect();
        let mut forward = vec![Vec::new(); names.len()];
        let mut reverse = forward.clone();
        for (a, b) in &self.edges {
            let (a, b) = (ids[a.as_str()], ids[b.as_str()]);
            forward[a].push(b);
            reverse[b].push(a);
        }
        // Iterative Kosaraju avoids compiler-stack growth for long bound chains.
        let mut seen = vec![false; names.len()];
        let mut finished = Vec::new();
        for start in 0..names.len() {
            let mut stack = vec![(start, false)];
            while let Some((v, exit)) = stack.pop() {
                if exit {
                    finished.push(v);
                    continue;
                }
                if seen[v] {
                    continue;
                }
                seen[v] = true;
                stack.push((v, true));
                for &w in forward[v].iter().rev() {
                    if !seen[w] {
                        stack.push((w, false));
                    }
                }
            }
        }
        let mut component = vec![usize::MAX; names.len()];
        let mut groups: Vec<Vec<usize>> = Vec::new();
        for &start in finished.iter().rev() {
            if component[start] != usize::MAX {
                continue;
            }
            let id = groups.len();
            let mut group = Vec::new();
            let mut stack = vec![start];
            component[start] = id;
            while let Some(v) = stack.pop() {
                group.push(v);
                for &w in &reverse[v] {
                    if component[w] == usize::MAX {
                        component[w] = id;
                        stack.push(w);
                    }
                }
            }
            group.sort_unstable();
            groups.push(group);
        }
        let mut dag = vec![BTreeSet::new(); groups.len()];
        for (v, successors) in forward.iter().enumerate() {
            for &w in successors {
                if component[v] != component[w] {
                    dag[component[v]].insert(component[w]);
                }
            }
        }
        let mut closure = Bounds::new();
        for (id, group) in groups.iter().enumerate() {
            let mut reachable = BTreeSet::new();
            let mut stack: Vec<_> = dag[id].iter().copied().collect();
            while let Some(c) = stack.pop() {
                if reachable.insert(c) {
                    stack.extend(dag[c].iter().copied());
                }
            }
            for &a in group {
                for &b in group {
                    if a != b
                        || group.len() > 1
                        || self.edges.contains(&(names[a].clone(), names[b].clone()))
                    {
                        closure.insert((names[a].clone(), names[b].clone()));
                    }
                }
                for &c in &reachable {
                    for &b in &groups[c] {
                        closure.insert((names[a].clone(), names[b].clone()));
                    }
                }
            }
        }
        let mut components: Vec<_> = groups
            .into_iter()
            .map(|g| g.into_iter().map(|i| names[i].clone()).collect::<Vec<_>>())
            .collect();
        components.sort();
        Solution {
            closure,
            components,
        }
    }
    /// A deterministic shortest witness using the original supplied edges.
    pub(crate) fn path(&self, long: &str, short: &str) -> Option<Vec<String>> {
        let mut previous: BTreeMap<String, Option<String>> =
            BTreeMap::from([(long.to_owned(), None)]);
        let mut queue = VecDeque::from([long.to_owned()]);
        while let Some(v) = queue.pop_front() {
            if v == short {
                let mut path = vec![v];
                while let Some(Some(p)) = previous.get(path.last().unwrap()) {
                    path.push(p.clone());
                }
                path.reverse();
                return Some(path);
            }
            for (a, b) in &self.edges {
                if a == &v && !previous.contains_key(b) {
                    previous.insert(b.clone(), Some(v.clone()));
                    queue.push_back(b.clone());
                }
            }
        }
        None
    }
    pub(crate) fn explain_missing(&self, long: &str, short: &str) -> String {
        let solution = self.solve();
        let known: Vec<_> = solution
            .closure
            .iter()
            .filter(|(a, b)| a == long && b != long)
            .map(|(_, b)| b.as_str())
            .collect();
        if known.is_empty() {
            format!(
                "no established outlives edge leaves {}; required endpoint is {}. A missing constraint is not inferred from this call",
                crate::runtime_types::lifetime_label_text(long),
                crate::runtime_types::lifetime_label_text(short)
            )
        } else {
            let target = known.last().unwrap();
            let path = self.path(long, target).unwrap();
            format!(
                "known outlives chain: {}; no established path reaches required endpoint {}. A missing constraint is not inferred from this call",
                path.iter()
                    .map(|s| crate::runtime_types::lifetime_label_text(s))
                    .collect::<Vec<_>>()
                    .join(" -> "),
                crate::runtime_types::lifetime_label_text(short)
            )
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    fn graph(edges: &[(&str, &str)]) -> LifetimeGraph {
        LifetimeGraph::new(
            &edges
                .iter()
                .map(|(a, b)| (a.to_string(), b.to_string()))
                .collect(),
        )
    }
    #[test]
    fn chains_cycles_and_anonymous_names_keep_exact_reachability() {
        let g = graph(&[
            ("a", "b"),
            ("b", "a"),
            ("b", "$anonymous"),
            ("$anonymous", "z"),
        ]);
        let s = g.solve();
        assert!(s.components.contains(&vec!["a".into(), "b".into()]));
        assert!(s.closure.contains(&("a".into(), "z".into())));
        assert!(!s.closure.contains(&("z".into(), "a".into())));
        assert_eq!(
            g.path("a", "z"),
            Some(vec![
                "a".into(),
                "b".into(),
                "$anonymous".into(),
                "z".into()
            ])
        );
        assert!(g.explain_missing("z", "a").contains("no established"));
        assert!(graph(&[]).solve().closure.is_empty());
    }
    #[test]
    fn exhaustive_four_node_graphs_match_independent_warshall_closure() {
        let pairs: Vec<_> = (0..4)
            .flat_map(|a| (0..4).filter(move |&b| a != b).map(move |b| (a, b)))
            .collect();
        for mask in 0..(1 << pairs.len()) {
            let mut matrix = [[false; 4]; 4];
            let mut edges = Bounds::new();
            for (bit, &(a, b)) in pairs.iter().enumerate() {
                if mask & (1 << bit) != 0 {
                    matrix[a][b] = true;
                    edges.insert((a.to_string(), b.to_string()));
                }
            }
            for k in 0..4 {
                for a in 0..4 {
                    for b in 0..4 {
                        matrix[a][b] |= matrix[a][k] && matrix[k][b];
                    }
                }
            }
            let s = LifetimeGraph::new(&edges).solve();
            for (a, row) in matrix.iter().enumerate() {
                for (b, &expected) in row.iter().enumerate() {
                    assert_eq!(
                        s.closure.contains(&(a.to_string(), b.to_string())),
                        expected,
                        "mask {mask}, {a}->{b}"
                    );
                }
            }
        }
    }
}
