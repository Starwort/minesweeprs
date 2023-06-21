use std::collections::{HashMap, HashSet};
use std::hash::Hash;

/// a! / b!
#[allow(clippy::cast_precision_loss)]
pub(crate) fn fact_div(a: usize, b: usize) -> f64 {
    #[allow(clippy::range_plus_one)]
    if a >= b {
        ((b + 1)..(a + 1)).product::<usize>() as f64
    } else {
        1.0 / fact_div(b, a)
    }
}

/// Return nCk
///
/// Resilient (though not immune) to integer overflow
pub(crate) fn choose(n: usize, k: usize) -> usize {
    if k > n {
        0
    } else if n <= 1 {
        // Optimise by far the most common case
        1
    } else {
        ((k.max(n - k) + 1)..=n).product::<usize>()
            / (2..=k.min(n - k)).product::<usize>()
    }
}

/// Perform a map-reduce on the data.
///
/// * `data` -> an iterable of data
/// * `emit_fn(datum)` -> an iterable of K-V pairings as (key, value)
/// * `reduce_fn(values)` -> applied to each list of values with the same key
pub(crate) fn map_reduce<T, U, K: Hash + Eq, V, EmitFn: Iterator<Item = (K, U)>>(
    data: impl Iterator<Item = T>,
    emit_fn: impl Fn(T) -> EmitFn,
    reduce_fn: impl Fn(Vec<U>) -> V,
) -> HashMap<K, V> {
    let mut result = HashMap::new();
    for val in data {
        for (key, value) in emit_fn(val) {
            result
                .entry(key)
                .or_insert_with(|| Vec::with_capacity(1))
                .push(value);
        }
    }
    result.into_iter().map(|(k, v)| (k, reduce_fn(v))).collect()
}

/// Pop and return an arbitrary item from a [`HashSet`].
pub(crate) fn pop<T: Hash + Eq + Clone>(set: &mut HashSet<T>) -> Option<T> {
    let value = set.iter().next()?.clone();
    set.remove(&value);
    Some(value)
}

/// Peek and return an arbitrary key from a [`HashMap`].
pub(crate) fn peek<K: Hash + Eq + Clone, V>(map: &HashMap<K, V>) -> Option<K> {
    map.keys().next().cloned()
}
/// Peek and return an arbitrary key from a [`HashMap`].
pub(crate) fn peek_set<T: Hash + Eq + Clone>(set: &HashSet<T>) -> Option<T> {
    set.iter().next().cloned()
}

/// Graph traversal algorithm -- given a graph and a node, return the set of
/// nodes that an be reached from `node`, including `node` itself
pub(crate) fn graph_traverse<T: Hash + Eq + Clone>(
    graph: &HashMap<T, HashSet<T>>,
    node: &T,
) -> HashSet<T> {
    fn traverse<T: Hash + Eq + Clone>(
        node: &T,
        graph: &HashMap<T, HashSet<T>>,
        visited: &mut HashSet<T>,
    ) {
        visited.insert(node.clone());
        for neighbour in &graph[node] {
            if !visited.contains(neighbour) {
                traverse(neighbour, graph, visited);
            }
        }
    }
    let mut visited = HashSet::new();
    traverse(node, graph, &mut visited);
    visited
}
