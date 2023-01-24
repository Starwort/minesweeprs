use std::cell::{Ref, RefCell, RefMut};
use std::cmp::{max, min};
use std::collections::hash_map::DefaultHasher;
use std::collections::{HashMap, HashSet};
use std::fmt::Debug;
use std::hash::{Hash, Hasher};
use std::ops::{Deref, Generator, GeneratorState, Sub};
use std::pin::Pin;
use std::rc::Rc;

use either::Either;

use crate::BoardInfo;

pub trait CustomInto<T> {
    fn into(self) -> T;
}

impl CustomInto<Either<BoardInfo, f64>> for BoardInfo {
    fn into(self) -> Either<BoardInfo, f64> {
        Either::Left(self)
    }
}
impl CustomInto<Either<BoardInfo, f64>> for f64 {
    fn into(self) -> Either<BoardInfo, f64> {
        Either::Right(self)
    }
}
impl<A, B> CustomInto<Either<A, B>> for Either<A, B> {
    fn into(self) -> Either<A, B> {
        self
    }
}

#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Default)]
pub struct Shared<T>(Rc<RefCell<T>>);
impl<T> Shared<T> {
    pub fn new(value: T) -> Self {
        Self(Rc::new(RefCell::new(value)))
    }

    pub fn borrow(&self) -> Ref<'_, T> {
        self.0.deref().borrow()
    }

    pub fn borrow_mut(&self) -> RefMut<T> {
        (*self.0).borrow_mut()
    }
}
impl<T> Debug for Shared<T>
where
    T: Debug,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Shared(")?;
        self.0.deref().borrow().fmt(f)?;
        write!(f, ")")
    }
}
impl<T, U> From<U> for Shared<T>
where
    Rc<RefCell<T>>: From<U>,
{
    fn from(value: U) -> Self {
        Self(value.into())
    }
}

pub fn fact_div(a: usize, b: usize) -> f64 {
    if a >= b {
        ((b + 1)..=a).map(|i| i as f64).product::<f64>()
    } else {
        1.0 / fact_div(b, a)
    }
}

pub fn comb(n: usize, k: usize) -> usize {
    ((max(k, n - k) + 1)..=n).product::<usize>()
        / (1..=min(k, n - k)).product::<usize>()
}

pub fn peek<T>(mut iter: impl Iterator<Item = T>) -> T {
    iter.next().expect("No items in iterator")
}

pub fn pop<T: Eq + Hash + Clone>(set: &mut HashSet<T>) -> Option<T> {
    if let Some(item) = set.iter().next().cloned() {
        set.remove(&item);
        Some(item)
    } else {
        None
    }
}

pub fn graph_traverse<T: Hash + Eq + Clone>(
    graph: &HashMap<T, HashSet<T>>,
    node: &T,
) -> HashSet<T> {
    let mut visited = HashSet::new();
    let mut to_visit = HashSet::from([node]);
    while let Some(node) = pop(&mut to_visit) {
        if visited.insert(node.clone()) {
            for neighbour in graph[node].iter() {
                if !visited.contains(neighbour) && !to_visit.contains(&neighbour) {
                    to_visit.insert(neighbour);
                }
            }
        }
    }
    visited
}

pub fn map_reduce<T, K: Hash + Eq, U, V, I: Iterator<Item = (K, U)>>(
    data: impl Iterator<Item = T>,
    emit: impl Fn(T) -> I,
    reduce: impl Fn(Vec<U>) -> V,
) -> HashMap<K, V> {
    let mut map = HashMap::new();
    for item in data {
        for (key, value) in emit(item) {
            map.entry(key).or_insert_with(Vec::new).push(value);
        }
    }
    map.into_iter()
        .map(|(key, values)| (key, reduce(values)))
        .collect()
}

pub struct GeneratorAdaptor<G: Generator<Yield = T, Return = ()> + Unpin, T> {
    inner: G,
}
impl<G: Generator<Yield = T, Return = ()> + Unpin, T> GeneratorAdaptor<G, T> {
    pub fn new(inner: G) -> Self {
        Self {
            inner,
        }
    }
}
impl<G: Generator<Yield = T, Return = ()> + Unpin, T> Iterator
    for GeneratorAdaptor<G, T>
{
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        match Pin::new(&mut self.inner).resume(()) {
            GeneratorState::Yielded(value) => Some(value),
            GeneratorState::Complete(()) => None,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenSet<T: Hash + Eq>(HashSet<T>);
impl<T: Hash + Eq> FrozenSet<T> {
    pub fn new() -> Self {
        Self(HashSet::new())
    }

    pub fn into_item(self) -> T {
        assert_eq!(self.len(), 1);
        self.into_iter().next().unwrap()
    }
}
impl<T: Hash + Eq> Default for FrozenSet<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Hash + Eq> Deref for FrozenSet<T> {
    type Target = HashSet<T>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<T: Hash + Eq, U> From<U> for FrozenSet<T>
where
    HashSet<T>: From<U>,
{
    fn from(set: U) -> Self {
        Self(set.into())
    }
}
impl<T: Hash + Eq, U> FromIterator<U> for FrozenSet<T>
where
    HashSet<T>: FromIterator<U>,
{
    fn from_iter<I: IntoIterator<Item = U>>(iter: I) -> Self {
        Self(HashSet::from_iter(iter))
    }
}
impl<T: Hash + Eq> Hash for FrozenSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut hash = 0;
        for item in self.iter() {
            let mut hasher = DefaultHasher::new();
            item.hash(&mut hasher);
            hash ^= hasher.finish();
        }
        state.write_u64(hash);
    }
}
impl<'a, T: Hash + Eq + Clone> Sub<&'a FrozenSet<T>> for &'a FrozenSet<T> {
    type Output = FrozenSet<T>;

    fn sub(self, rhs: Self) -> Self::Output {
        FrozenSet(self.0.difference(&rhs.0).cloned().collect())
    }
}
impl<T: Hash + Eq> IntoIterator for FrozenSet<T> {
    type IntoIter = <HashSet<T> as IntoIterator>::IntoIter;
    type Item = T;

    fn into_iter(self) -> Self::IntoIter {
        self.0.into_iter()
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct FrozenMap<K: Hash + Eq, V>(HashMap<K, V>);
impl<K: Hash + Eq, V> FrozenMap<K, V> {
    pub fn into_inner(self) -> HashMap<K, V> {
        self.0
    }
}
impl<K: Hash + Eq, V> Deref for FrozenMap<K, V> {
    type Target = HashMap<K, V>;

    fn deref(&self) -> &Self::Target {
        &self.0
    }
}
impl<K: Hash + Eq, V, U> From<U> for FrozenMap<K, V>
where
    HashMap<K, V>: From<U>,
{
    fn from(map: U) -> Self {
        Self(map.into())
    }
}
impl<K: Hash + Eq, V, U> FromIterator<U> for FrozenMap<K, V>
where
    HashMap<K, V>: FromIterator<U>,
{
    fn from_iter<I: IntoIterator<Item = U>>(iter: I) -> Self {
        Self(HashMap::from_iter(iter))
    }
}
impl<K: Hash + Eq, V: Hash> Hash for FrozenMap<K, V> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        let mut hash = 0;
        for (key, value) in self.iter() {
            let mut hasher = DefaultHasher::new();
            key.hash(&mut hasher);
            value.hash(&mut hasher);
            hash ^= hasher.finish();
        }
        state.write_u64(hash);
    }
}
