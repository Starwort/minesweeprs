#![feature(generators, generator_trait)]
#![allow(clippy::too_many_lines)]
use std::cmp::{min, Ordering};
use std::collections::{BinaryHeap, HashMap, HashSet, VecDeque};
use std::fmt::Debug;
use std::hash::Hash;
use std::iter::{empty, once};
use std::rc::Rc;

use either::Either;
use internal_util::{
    comb,
    fact_div,
    graph_traverse,
    map_reduce,
    peek,
    pop,
    CustomInto,
    FrozenMap,
    FrozenSet,
    GeneratorAdaptor,
    Shared,
};
use itertools::Itertools;
mod internal_util;
pub mod util;

pub trait Cell: Hash + Eq + Clone + Debug {}
impl<T: Hash + Eq + Clone + Debug> Cell for T {
}

#[derive(Clone, Copy, Debug, Hash, PartialEq, Eq)]
pub struct BoardInfo {
    pub total_cells: usize,
    pub total_mines: usize,
}

pub type Error = &'static str;

pub fn solve<T: Cell>(
    rules: &[Rule<T>],
    mine_prevalence: impl CustomInto<Either<BoardInfo, f64>>,
    other_tag: impl Into<Rc<T>>,
) -> Result<HashMap<Rc<T>, f64>, Error> {
    let mine_prevalence = mine_prevalence.into();
    let (internal_rules, all_cells) = condense_supercells(rules)?;
    let mut reduced = reduce_rules(&internal_rules);

    let mut determined = reduced
        .iter()
        .filter(|r| r.is_trivial())
        .cloned()
        .collect::<HashSet<_>>();
    reduced.retain(|r| !r.is_trivial());

    let mut fronts = permute_and_interfere(Shared::new(reduced))?.split_fronts();

    determined.extend(
        fronts
            .iter()
            .filter(|f| f.is_trivial())
            .map(PermutedRuleset::trivial_rule),
    );
    fronts.retain(|f| !f.is_trivial());

    let mut stats = fronts
        .into_iter()
        .map(|f| enumerate_front(f).map(Shared::new))
        .collect::<Result<Vec<_>, _>>()?;
    stats.extend(determined.into_iter().map(|r| Shared::new(r.tally())));

    let cell_probs = cell_probabilities(stats, mine_prevalence, all_cells)?;
    Ok(expand_cells(cell_probs, other_tag.into()).collect())
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
pub struct Rule<T: Cell> {
    num_mines: usize,
    cells: FrozenSet<Rc<T>>,
}
impl<T: Cell> Rule<T> {
    pub fn new(num_mines: usize, cells: impl IntoIterator<Item = T>) -> Self {
        Self {
            num_mines,
            cells: cells.into_iter().map(Rc::new).collect(),
        }
    }

    fn condensed(
        &self,
        rule_supercells_map: &HashMap<Self, Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>>,
    ) -> Result<Rc<InternalRule<T>>, Error> {
        InternalRule::new(
            self.num_mines,
            // default to handle degenerate rules
            rule_supercells_map
                .get(self)
                .cloned()
                .unwrap_or_else(|| Rc::new(FrozenSet::new())),
            self.cells.len(),
        )
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Hash)]
struct InternalRule<T: Cell> {
    num_mines: usize,
    num_cells: usize,
    super_cells: Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
}
impl<T: Cell> InternalRule<T> {
    pub fn new(
        num_mines: usize,
        super_cells: Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
        num_cells: usize,
    ) -> Result<Rc<Self>, Error> {
        if num_mines <= num_cells {
            Ok(Rc::new(Self {
                num_mines,
                num_cells,
                super_cells,
            }))
        } else {
            Err("Rule with more mines than cells")
        }
    }

    pub fn decompose<'a>(
        self: &'a Rc<Self>,
    ) -> Box<dyn Iterator<Item = Rc<Self>> + 'a> {
        if self.num_mines == 0 || self.num_mines == self.num_cells {
            Box::new(self.super_cells.iter().map(|super_cell| {
                let size = super_cell.len();
                InternalRule::new(
                    if self.num_mines > 0 { size } else { 0 },
                    Rc::new([Rc::clone(super_cell)].into()),
                    size,
                )
                .expect("Decomposing a rule should always be valid")
            }))
        } else {
            Box::new(once(Rc::clone(self)))
        }
    }

    pub fn subtract(&self, other: &Self) -> Rc<Self> {
        Self::new(
            self.num_mines - other.num_mines,
            Rc::new((&*self.super_cells) - &other.super_cells),
            self.num_cells - other.num_cells,
        )
        .expect("Subtracting a rule should always be valid")
    }

    pub fn permute(&self) -> impl Iterator<Item = Rc<Permutation<T>>> + '_ {
        fn permute<'a, T: Cell + 'a>(
            count: usize,
            cells: &'a mut VecDeque<Rc<FrozenSet<Rc<T>>>>,
            permu: HashSet<(Rc<FrozenSet<Rc<T>>>, usize)>,
        ) -> Box<dyn Iterator<Item = Rc<Permutation<T>>> + 'a> {
            if count == 0 {
                Box::new(once(Rc::new(Permutation::new(
                    permu
                        .union(&cells.iter().map(|cell| (Rc::clone(cell), 0)).collect())
                        .cloned(),
                ))))
            } else {
                let remaining_size = cells.iter().map(|cell| cell.len()).sum::<usize>();
                if remaining_size == count {
                    Box::new(once(Rc::new(Permutation::new(
                        permu
                            .union(
                                &cells
                                    .iter()
                                    .map(|cell| (Rc::clone(cell), cell.len()))
                                    .collect(),
                            )
                            .cloned(),
                    ))))
                } else if remaining_size >= count {
                    let cell = cells.pop_front().expect(concat!(
                        "count >= 1, remaining_size >= count, so",
                        " cells must not be empty",
                    ));
                    // TODO: remove this generator
                    Box::new(GeneratorAdaptor::new(move || {
                        for multiplicity in (0..=min(count, cell.len())).rev() {
                            for i in permute(
                                count - multiplicity,
                                cells,
                                permu
                                    .union(&[(Rc::clone(&cell), multiplicity)].into())
                                    .cloned()
                                    .collect(),
                            ) {
                                yield i;
                            }
                        }
                    }))
                } else {
                    Box::new(empty())
                }
            }
        }

        let mut cells = self.super_cells.iter().cloned().collect();
        permute(self.num_mines, &mut cells, HashSet::new())
            .collect_vec()
            .into_iter()
    }

    pub fn is_subule_of(&self, other: &Self) -> bool {
        self.super_cells.is_subset(&other.super_cells)
    }

    pub fn is_trivial(&self) -> bool {
        self.super_cells.len() == 1
    }

    pub fn tally(&self) -> FrontTally<T> {
        FrontTally::from_rule(self)
    }
}

fn condense_supercells<T: Cell>(
    rules: &[Rule<T>],
) -> Result<(Vec<Rc<InternalRule<T>>>, Vec<Rc<FrozenSet<Rc<T>>>>), Error> {
    // For each cell, the rules it appears in
    let cell_rules_map = map_reduce(
        rules.iter(),
        |rule| {
            rule.cells
                .iter()
                .map(|cell| (Rc::clone(cell), rule.clone()))
        },
        |rules| Rc::new(rules.into_iter().collect::<FrozenSet<_>>()),
    );

    // For each group of rules a cell appears in, the cells that share those rules
    // (these cells thus only ever appear together in the same rules)
    let rules_supercell_map = map_reduce(
        cell_rules_map.into_iter(),
        |(cell, rules)| [(rules, cell)].into_iter(),
        |cells| Rc::new(cells.into_iter().collect::<FrozenSet<_>>()),
    );

    // For each original rule, the super cells appearing in that rule
    let rule_supercells_map = map_reduce(
        rules_supercell_map.iter(),
        |(rules, cell)| {
            rules
                .iter()
                .map(|rule| (rule.clone(), Rc::clone(cell)))
                .collect_vec()
                .into_iter()
        },
        |cells| Rc::new(cells.into_iter().collect::<FrozenSet<_>>()),
    );
    Ok((
        rules
            .iter()
            .map(|rule| rule.condensed(&rule_supercells_map))
            .collect::<Result<Vec<_>, Error>>()?,
        rules_supercell_map.into_values().collect(),
    ))
}

fn reduce_rules<T: Cell>(
    rules: &[Rc<InternalRule<T>>],
) -> HashSet<Rc<InternalRule<T>>> {
    let mut reducer = RuleReducer::new();
    reducer.add_rules(rules.iter());
    reducer.reduce_all()
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Reduceable<T: Cell> {
    super_rule: Rc<InternalRule<T>>,
    sub_rule: Rc<InternalRule<T>>,
}
impl<T: Cell> Reduceable<T> {
    pub fn new(super_rule: Rc<InternalRule<T>>, sub_rule: Rc<InternalRule<T>>) -> Self {
        Self {
            super_rule,
            sub_rule,
        }
    }

    pub fn metric(&self) -> (usize, usize, usize) {
        let num_reduced_cells = self.super_rule.num_cells - self.sub_rule.num_cells;
        let num_reduced_mines = self.super_rule.num_mines - self.sub_rule.num_mines;
        (
            self.super_rule.num_cells,
            self.sub_rule.num_cells,
            num_reduced_mines.abs_diff(num_reduced_cells / 2),
        )
    }

    pub fn reduce(&self) -> Rc<InternalRule<T>> {
        self.super_rule.subtract(&self.sub_rule)
    }

    pub fn contained_within(&self, rules: &HashSet<Rc<InternalRule<T>>>) -> bool {
        rules.contains(&self.super_rule) && rules.contains(&self.sub_rule)
    }
}
impl<T: Cell> Ord for Reduceable<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.metric().cmp(&other.metric())
    }
}
impl<T: Cell> PartialOrd for Reduceable<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct CellRulesMap<T: Cell> {
    map: HashMap<Rc<FrozenSet<Rc<T>>>, Shared<HashSet<Rc<InternalRule<T>>>>>,
    rules: HashSet<Rc<InternalRule<T>>>,
}
impl<T: Cell> CellRulesMap<T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            rules: HashSet::new(),
        }
    }

    pub fn add_rules(&mut self, rules: impl Iterator<Item = Rc<InternalRule<T>>>) {
        for rule in rules {
            self.add_rule(rule);
        }
    }

    pub fn add_rule(&mut self, rule: Rc<InternalRule<T>>) {
        for super_cell in rule.super_cells.iter() {
            (*self
                .map
                .entry(Rc::clone(super_cell))
                .or_insert_with(|| Shared::new(HashSet::new())))
            .borrow_mut()
            .insert(Rc::clone(&rule));
        }
        self.rules.insert(rule);
    }

    pub fn remove_rule(&mut self, rule: &InternalRule<T>) {
        for super_cell in rule.super_cells.iter() {
            self.map
                .get(super_cell)
                .expect("Attempted to remove a rule that was not present")
                .borrow_mut()
                .remove(rule);
        }
        self.rules.remove(rule);
    }

    pub fn overlapping_rules(
        &self,
        rule: &InternalRule<T>,
    ) -> HashSet<Rc<InternalRule<T>>> {
        let default = Shared::new(HashSet::new());
        let mut rules = rule
            .super_cells
            .iter()
            .flat_map(|super_cell| {
                self.map
                    .get(super_cell)
                    .unwrap_or(&default)
                    .borrow()
                    .iter()
                    .cloned()
                    .collect_vec()
                    .into_iter()
            })
            .collect::<HashSet<_>>();
        rules.remove(rule);
        rules
    }

    pub fn interference_edges(
        &self,
    ) -> HashSet<(Rc<InternalRule<T>>, Rc<InternalRule<T>>)> {
        self.rules
            .iter()
            .flat_map(|rule| {
                self.overlapping_rules(rule)
                    .into_iter()
                    .map(|overlapping| (Rc::clone(rule), overlapping))
            })
            .collect()
    }

    pub fn partition(&self) -> HashSet<Rc<FrozenSet<Rc<InternalRule<T>>>>> {
        let mut related_rules: HashMap<_, _> = self
            .rules
            .iter()
            .map(|rule| (Rc::clone(rule), self.overlapping_rules(rule)))
            .collect();
        let mut partitions = HashSet::new();
        while !related_rules.is_empty() {
            let start = peek(related_rules.keys());
            let partition = graph_traverse(&related_rules, start);
            for rule in &partition {
                related_rules.remove(rule);
            }
            partitions.insert(Rc::new(partition.into()));
        }
        partitions
    }

    pub fn super_cells(&self) -> FrozenSet<Rc<FrozenSet<Rc<T>>>> {
        self.map.keys().cloned().collect()
    }
}

#[derive(Clone, Debug)]
struct RuleReducer<T: Cell> {
    active_rules: HashSet<Rc<InternalRule<T>>>,
    cell_rules_map: CellRulesMap<T>,
    candidate_reductions: BinaryHeap<Reduceable<T>>,
}
impl<T: Cell> RuleReducer<T> {
    pub fn new() -> Self {
        Self {
            active_rules: HashSet::new(),
            cell_rules_map: CellRulesMap::new(),
            candidate_reductions: BinaryHeap::new(),
        }
    }

    pub fn add_rules<'a>(
        &mut self,
        rules: impl Iterator<Item = &'a Rc<InternalRule<T>>>,
    ) where
        T: 'a,
    {
        for rule in rules {
            self.add_rule(rule);
        }
    }

    pub fn add_rule(&mut self, rule: &Rc<InternalRule<T>>) {
        for base_rule in rule.decompose() {
            self.add_base_rule(&base_rule);
        }
    }

    pub fn add_base_rule(&mut self, rule: &Rc<InternalRule<T>>) {
        self.active_rules.insert(Rc::clone(rule));
        self.cell_rules_map.add_rule(Rc::clone(rule));
        self.update_reduceables(rule);
    }

    pub fn add_reduceable(&mut self, reduction: Reduceable<T>) {
        self.candidate_reductions.push(reduction);
    }

    pub fn update_reduceables(&mut self, rule: &Rc<InternalRule<T>>) {
        for overlapping in self.cell_rules_map.overlapping_rules(rule) {
            if overlapping.is_subule_of(rule) {
                // This path is followed if the rules are equivalent
                self.add_reduceable(Reduceable::new(Rc::clone(rule), overlapping));
            } else if rule.is_subule_of(&overlapping) {
                self.add_reduceable(Reduceable::new(overlapping, Rc::clone(rule)));
            }
        }
    }

    pub fn remove_rule(&mut self, rule: &InternalRule<T>) {
        self.active_rules.remove(rule);
        self.cell_rules_map.remove_rule(rule);
    }

    pub fn get_next_reduction(&mut self) -> Option<Reduceable<T>> {
        while let Some(reduction) = self.candidate_reductions.pop() {
            if reduction.contained_within(&self.active_rules) {
                return Some(reduction);
            }
        }
        None
    }

    pub fn reduce(&mut self, reduction: Reduceable<T>) {
        let reduced_rule = reduction.reduce();
        self.remove_rule(&reduction.super_rule);
        self.add_rule(&reduced_rule);
    }

    pub fn reduce_all(mut self) -> HashSet<Rc<InternalRule<T>>> {
        while let Some(reduction) = self.get_next_reduction() {
            self.reduce(reduction);
        }
        self.active_rules
    }
}

#[derive(Clone, Debug, Hash, PartialEq, Eq)]
struct Permutation<T: Cell> {
    mapping: FrozenMap<Rc<FrozenSet<Rc<T>>>, usize>,
}
impl<T: Cell> Permutation<T> {
    pub fn new(
        mapping: impl IntoIterator<Item = (Rc<FrozenSet<Rc<T>>>, usize)>,
    ) -> Self {
        Self {
            mapping: mapping.into_iter().collect(),
        }
    }

    pub fn subset(&self, subcells: impl Iterator<Item = Rc<FrozenSet<Rc<T>>>>) -> Self {
        Self::new(subcells.map(|cell| {
            let mapped = self.mapping[&cell];
            (cell, mapped)
        }))
    }

    pub fn is_compatible(&self, other: &Self) -> bool {
        let overlap = self
            .cells()
            .intersection(&other.cells())
            .cloned()
            .collect::<HashSet<_>>();
        self.subset(overlap.iter().cloned()) == other.subset(overlap.into_iter())
    }

    pub fn combine(&self, other: &Self) -> Self {
        assert!(self
            .mapping
            .iter()
            .filter(|(cell, _)| other.mapping.contains_key(*cell))
            .all(|(cell, value)| other.mapping[cell] == *value));
        let mut map = self.mapping.clone().into_inner();
        for (k, &v) in other.mapping.iter() {
            map.insert(Rc::clone(k), v);
        }
        Self::new(map)
    }

    pub fn k(&self) -> usize {
        self.mapping.values().sum::<usize>()
    }

    pub fn cells(&self) -> HashSet<Rc<FrozenSet<Rc<T>>>> {
        self.mapping.keys().cloned().collect()
    }

    pub fn multiplicity(&self) -> usize {
        self.mapping
            .iter()
            .map(|(super_cell, &k)| comb(super_cell.len(), k))
            .product::<usize>()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PermutationSet<T: Cell> {
    super_cells: Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
    k: usize,
    permutations: HashSet<Rc<Permutation<T>>>,
    constrained: bool,
}
impl<T: Cell> PermutationSet<T> {
    pub fn new(
        super_cells: Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
        k: usize,
        permutations: impl IntoIterator<Item = Rc<Permutation<T>>>,
    ) -> Self {
        Self {
            super_cells,
            k,
            permutations: permutations.into_iter().collect(),
            constrained: false,
        }
    }

    pub fn from_rule(rule: &InternalRule<T>) -> Self {
        Self::new(Rc::clone(&rule.super_cells), rule.num_mines, rule.permute())
    }

    pub fn to_rule(&self) -> Rc<InternalRule<T>> {
        InternalRule::new(
            self.k,
            Rc::clone(&self.super_cells),
            self.super_cells
                .iter()
                .map(|super_cell| super_cell.len())
                .sum::<usize>(),
        )
        .expect("Should be impossible to create an invalid rule from a PermutationSet")
    }

    pub fn iter(&self) -> impl Iterator<Item = &Rc<Permutation<T>>> {
        self.permutations.iter()
    }

    pub fn contains(&self, p: &Permutation<T>) -> bool {
        self.permutations.contains(p)
    }

    pub fn remove(&mut self, permu: &Permutation<T>) {
        self.permutations.remove(permu);
        self.constrained = true;
    }

    pub fn is_empty(&self) -> bool {
        self.permutations.is_empty()
    }

    pub fn compatible(&self, permu: &Permutation<T>) -> Self {
        Self::new(
            Rc::clone(&self.super_cells),
            self.k,
            self.permutations
                .iter()
                .filter(|p| p.is_compatible(permu))
                .cloned(),
        )
    }

    pub fn subset(
        &self,
        cell_subset: &Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
    ) -> Option<Self> {
        let permu_subset = self
            .permutations
            .iter()
            .map(|p| Rc::new(p.subset(cell_subset.iter().cloned())))
            .collect::<HashSet<_>>();
        let mut k_sub = permu_subset.iter().map(|p| p.k()).collect::<HashSet<_>>();
        if k_sub.len() == 1 {
            Some(Self::new(
                Rc::clone(cell_subset),
                pop(&mut k_sub).unwrap(),
                permu_subset,
            ))
        } else {
            None
        }
    }

    pub fn decompose(&self) -> Vec<Self> {
        if self.constrained {
            self.force_decompose(1)
        } else {
            vec![self.clone()]
        }
    }

    fn force_decompose(&self, k_floor: usize) -> Vec<Self> {
        for k in k_floor..=(self.super_cells.len() / 2) {
            for cell_subset in self.super_cells.iter().combinations(k) {
                let cell_subset =
                    Rc::new(cell_subset.into_iter().cloned().collect::<FrozenSet<_>>());
                let Some((permu_subset, permu_remainder)) = self.split(&cell_subset)
                else { continue; };
                let mut divisors = vec![permu_subset];
                divisors.extend(permu_remainder.force_decompose(k));
                return divisors;
            }
        }
        vec![self.clone()]
    }

    fn split(
        &self,
        cell_subset: &Rc<FrozenSet<Rc<FrozenSet<Rc<T>>>>>,
    ) -> Option<(Self, Self)> {
        let cell_remainder = self
            .super_cells
            .difference(cell_subset)
            .cloned()
            .collect::<FrozenSet<_>>();
        let permu_subset = self.subset(cell_subset)?;

        let mut permu_remainders = map_reduce(
            self.permutations.iter().cloned(),
            |p| [(p.subset(cell_subset.iter().cloned()), p)].into_iter(),
            |pv| {
                Rc::new(
                    pv.into_iter()
                        .map(|p| Rc::new(p.subset(cell_remainder.iter().cloned())))
                        .collect::<FrozenSet<_>>(),
                )
            },
        )
        .into_values()
        .collect::<HashSet<_>>();

        if permu_remainders.len() == 1 {
            let permu_remainders = pop(&mut permu_remainders).unwrap();
            let other_k = permu_subset.k;
            Some((
                permu_subset,
                Self::new(
                    Rc::new(cell_remainder),
                    self.k - other_k,
                    permu_remainders.iter().cloned(),
                ),
            ))
        } else {
            None
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
struct PermutedRuleset<T: Cell> {
    rules: Shared<HashSet<Rc<InternalRule<T>>>>,
    cell_rules_map: CellRulesMap<T>,
    super_cells: FrozenSet<Rc<FrozenSet<Rc<T>>>>,
    permu_map: HashMap<Rc<InternalRule<T>>, Shared<PermutationSet<T>>>,
}
impl<T: Cell> PermutedRuleset<T> {
    pub fn new(
        rules: &Shared<HashSet<Rc<InternalRule<T>>>>,
        permu_map: Option<&HashMap<Rc<InternalRule<T>>, Shared<PermutationSet<T>>>>,
    ) -> Self {
        let mut cell_rules_map = CellRulesMap::new();
        cell_rules_map.add_rules(rules.borrow().iter().cloned());
        let super_cells = cell_rules_map.super_cells();
        Self {
            rules: Shared::clone(rules),
            cell_rules_map,
            super_cells,
            permu_map: match permu_map {
                Some(permu_map) => {
                    rules
                        .borrow()
                        .iter()
                        .map(|rule| (Rc::clone(rule), Shared::clone(&permu_map[rule])))
                        .collect()
                },
                None => {
                    rules
                        .borrow()
                        .iter()
                        .map(|rule| {
                            (
                                Rc::clone(rule),
                                Shared::new(PermutationSet::from_rule(rule)),
                            )
                        })
                        .collect()
                },
            },
        }
    }

    pub fn cross_eliminate(&mut self) -> Result<(), Error> {
        let mut interferences = self.cell_rules_map.interference_edges();
        while let Some((rule, overlapping)) = pop(&mut interferences) {
            let mut changed = false;
            for permu in self.permu_map[&rule]
                .borrow()
                .iter()
                .cloned()
                .collect::<Vec<_>>()
            {
                // Copy the set into a list so we can mutate it
                if self.permu_map[&overlapping]
                    .borrow()
                    .compatible(&permu)
                    .is_empty()
                {
                    self.permu_map[&rule].borrow_mut().remove(&permu);
                    changed = true;
                }
            }

            if self.permu_map[&rule].borrow().is_empty() {
                return Err(
                    "Rule is constrained such that it has no valid mine permutations"
                );
            } else if changed {
                interferences.extend(
                    self.cell_rules_map
                        .overlapping_rules(&rule)
                        .into_iter()
                        .map(|other| (other, Rc::clone(&rule))),
                );
            }
        }
        Ok(())
    }

    pub fn rereduce(&mut self) {
        let mut superseded_rules = HashSet::new();
        let mut decompositions = HashMap::new();
        for (rule, permu_set) in self.permu_map.iter() {
            let decomp = permu_set.borrow().decompose();
            if decomp.len() > 1 {
                superseded_rules.insert(Rc::clone(rule));
                decompositions.extend(
                    decomp
                        .into_iter()
                        .map(|dc| (Rc::clone(&dc.super_cells), dc)),
                );
            }
        }

        for rule in superseded_rules {
            self.remove_rule(rule);
        }
        for permu_set in decompositions.into_values() {
            self.add_permu_set(permu_set);
        }
    }

    pub fn remove_rule(&mut self, rule: Rc<InternalRule<T>>) {
        self.rules.borrow_mut().remove(&rule);
        self.cell_rules_map.remove_rule(&rule);
        self.permu_map.remove(&rule);
    }

    pub fn add_permu_set(&mut self, permu_set: PermutationSet<T>) {
        let rule = permu_set.to_rule();
        self.rules.borrow_mut().insert(Rc::clone(&rule));
        self.cell_rules_map.add_rule(Rc::clone(&rule));
        self.permu_map.insert(rule, Shared::new(permu_set));
    }

    pub fn filter(&self, rule_subset: &Shared<HashSet<Rc<InternalRule<T>>>>) -> Self {
        Self::new(rule_subset, Some(&self.permu_map))
    }

    pub fn split_fronts(&self) -> Vec<Self> {
        self.cell_rules_map
            .partition()
            .into_iter()
            .map(|rule_subset| {
                self.filter(&Shared::new(rule_subset.iter().cloned().collect()))
            })
            .collect()
    }

    pub fn is_trivial(&self) -> bool {
        self.rules.borrow().len() == 1
    }

    pub fn trivial_rule(&self) -> Rc<InternalRule<T>> {
        assert!(self.is_trivial());
        let singleton = peek(self.rules.borrow().iter().cloned());
        assert!(singleton.is_trivial());
        singleton
    }

    pub fn enumerate(&self) -> Box<dyn Iterator<Item = Permutation<T>> + '_> {
        EnumerationState::new(self).enumerate()
    }
}

fn permute_and_interfere<T: Cell>(
    rules: Shared<HashSet<Rc<InternalRule<T>>>>,
) -> Result<PermutedRuleset<T>, Error> {
    let mut permuted_ruleset = PermutedRuleset::new(&rules, None);
    permuted_ruleset.cross_eliminate()?;
    permuted_ruleset.rereduce();
    Ok(permuted_ruleset)
}

#[derive(Debug, PartialEq, Eq)]
struct EnumerationState<'a, T: Cell> {
    fixed: HashSet<Rc<Permutation<T>>>,
    ruleset: &'a PermutedRuleset<T>,
    free: HashMap<Rc<InternalRule<T>>, Shared<HashSet<Rc<Permutation<T>>>>>,
    compatible_rule_index:
        HashMap<(Rc<Permutation<T>>, Rc<InternalRule<T>>), Rc<PermutationSet<T>>>,
}
impl<'a, T: Cell> EnumerationState<'a, T> {
    pub fn new(ruleset: &'a PermutedRuleset<T>) -> Self {
        let mut rv = Self {
            fixed: HashSet::new(),
            ruleset,
            free: ruleset
                .permu_map
                .iter()
                .map(|(rule, permu_set)| {
                    (
                        Rc::clone(rule),
                        Shared::new(permu_set.borrow().iter().cloned().collect()),
                    )
                })
                .collect(),
            compatible_rule_index: HashMap::new(),
        };
        rv.build_compatibility_index(&ruleset.permu_map);
        rv
    }

    pub fn overlapping_rules(
        &self,
        rule: &InternalRule<T>,
    ) -> HashSet<Rc<InternalRule<T>>> {
        self.ruleset.cell_rules_map.overlapping_rules(rule)
    }

    pub fn build_compatibility_index(
        &mut self,
        map: &HashMap<Rc<InternalRule<T>>, Shared<PermutationSet<T>>>,
    ) {
        for (rule, permu_set) in map.iter() {
            for permu in permu_set.borrow().iter() {
                for overlapping in self.overlapping_rules(rule) {
                    let v = Rc::new(map[&overlapping].borrow().compatible(permu));
                    self.compatible_rule_index
                        .insert((Rc::clone(permu), overlapping), v);
                }
            }
        }
    }

    pub fn is_complete(&self) -> bool {
        self.free.is_empty()
    }

    pub fn iter(&self) -> impl Iterator<Item = EnumerationState<'a, T>> {
        let state = self.clone();
        let rule = Rc::clone(peek(state.free.keys()));
        let permus = self.free[&rule].borrow().clone();
        permus
            .into_iter()
            .filter_map(move |permu| state.propagate(&rule, permu))
    }

    pub fn propagate(
        &self,
        rule: &Rc<InternalRule<T>>,
        permu: Rc<Permutation<T>>,
    ) -> Option<Self> {
        let mut state = self.clone();
        state.force_propagate(rule, permu)?;
        Some(state)
    }

    fn force_propagate(
        &mut self,
        rule: &Rc<InternalRule<T>>,
        permu: Rc<Permutation<T>>,
    ) -> Option<()> {
        self.fixed.insert(Rc::clone(&permu));
        self.free.remove(rule)?;

        // Constrain overlapping rules
        let mut cascades = Vec::new();
        for related_rule in self
            .overlapping_rules(rule)
            .into_iter()
            .filter(|r| self.free.contains_key(r))
            .collect_vec()
        {
            // PermutationSet of the related rule, constrained *only* by the
            // rule/permutation just fixed
            let allowed_permus = self
                .compatible_rule_index
                .get(&(Rc::clone(&permu), Rc::clone(&related_rule)))?;
            // Further constrain the related rule with this new set -- is now properly
            // constrained by fixed rules
            self.free
                .get(&related_rule)?
                .borrow_mut()
                .retain(|p| allowed_permus.contains(p));

            let linked_permus = self.free.get(&related_rule)?;
            if linked_permus.borrow().is_empty() {
                return None;
            } else if linked_permus.borrow().len() == 1 {
                // Only one possibility - constrain further
                cascades.push((
                    Rc::clone(&related_rule),
                    peek(linked_permus.borrow().iter().cloned()),
                ));
            }
        }

        // Cascade if any other rules are now fully constrained
        for (related_rule, constrained_permu) in cascades {
            // May have already been constrained by a prior recursive call
            if self.free.contains_key(&related_rule) {
                self.force_propagate(&related_rule, constrained_permu)?;
            }
        }
        Some(())
    }

    pub fn mine_config(&self) -> Permutation<T> {
        self.fixed
            .iter()
            .fold(Permutation::new(empty()), |a, b| a.combine(b))
    }

    pub fn enumerate(&self) -> Box<dyn Iterator<Item = Permutation<T>> + 'a> {
        if self.is_complete() {
            Box::new(std::iter::once(self.mine_config()))
        } else {
            Box::new(self.iter().flat_map(|s| s.enumerate()))
        }
    }
}
impl<'a, T: Cell> Clone for EnumerationState<'a, T> {
    fn clone(&self) -> Self {
        Self {
            fixed: self.fixed.clone(),
            ruleset: self.ruleset,
            free: self
                .free
                .iter()
                .map(|(k, v)| (Rc::clone(k), Shared::new(v.borrow().clone())))
                .collect(),
            compatible_rule_index: self.compatible_rule_index.clone(),
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
struct FrontTally<T: Cell> {
    subtallies: HashMap<usize, Shared<FrontSubtally<T>>>,
}
impl<T: Cell> FrontTally<T> {
    pub fn new(data: impl Iterator<Item = (usize, Shared<FrontSubtally<T>>)>) -> Self {
        Self {
            subtallies: data.collect(),
        }
    }

    pub fn tally(&mut self, front: PermutedRuleset<T>) -> Result<(), Error> {
        for config in front.enumerate() {
            (self
                .subtallies
                .entry(config.k())
                .or_insert_with(|| Shared::new(FrontSubtally::new())))
            .borrow_mut()
            .add(&config);
        }

        if self.subtallies.is_empty() {
            return Err("Mine front has no possible configurations");
        }

        self.finalise();

        Ok(())
    }

    pub fn finalise(&mut self) {
        for subtally in self.subtallies.values() {
            subtally.borrow_mut().finalise();
        }
    }

    pub fn min_mines(&self) -> usize {
        self.subtallies
            .keys()
            .copied()
            .min()
            .expect("Mine front has no possible configurations")
    }

    pub fn max_mines(&self) -> usize {
        self.subtallies
            .keys()
            .copied()
            .max()
            .expect("Mine front has no possible configurations")
    }

    pub fn is_static(&self) -> bool {
        self.subtallies.len() == 1
    }

    pub fn iter(&self) -> impl Iterator<Item = (usize, Shared<FrontSubtally<T>>)> + '_ {
        self.subtallies.iter().map(|(&k, v)| (k, Shared::clone(v)))
    }

    pub fn normalise(&mut self) {
        let total = self
            .subtallies
            .values()
            .map(|s| s.borrow().total)
            .sum::<f64>();
        for subtally in self.subtallies.values() {
            let mut subtally = subtally.borrow_mut();
            subtally.total /= total;
            subtally.normalised = true;
        }
    }

    pub fn collapse(
        &mut self,
    ) -> HashMap<Either<Rc<FrozenSet<Rc<T>>>, UnchartedCell>, f64> {
        self.normalise();
        let collapsed = map_reduce(
            self.subtallies.values(),
            |subtally| subtally.borrow().collapse().collect_vec().into_iter(),
            |values| values.into_iter().sum(),
        );
        collapsed
    }

    pub fn scale_weights(
        &mut self,
        scale_func: impl Fn(usize) -> Result<f64, Error>,
    ) -> Result<(), Error> {
        for (&num_mines, subtally) in self.subtallies.iter() {
            subtally.borrow_mut().total *= scale_func(num_mines)?;
        }
        Ok(())
    }

    pub fn update_weights(&mut self, weights: &HashMap<usize, f64>) {
        for (&num_mines, subtally) in self.subtallies.iter() {
            subtally.borrow_mut().total *=
                weights.get(&num_mines).copied().unwrap_or(0.0);
        }
    }

    pub fn from_rule(rule: &InternalRule<T>) -> Self {
        assert!(rule.is_trivial());
        Self::new(
            [(
                rule.num_mines,
                Shared::new(FrontSubtally::from_data(
                    comb(rule.num_cells, rule.num_mines) as f64,
                    [(
                        Either::Left(peek(rule.super_cells.iter().cloned())),
                        rule.num_mines as f64,
                    )]
                    .into_iter(),
                )),
            )]
            .into_iter(),
        )
    }

    pub fn for_other(
        num_uncharted_cells: usize,
        mine_totals: &HashMap<usize, f64>,
    ) -> Self {
        let meta_cell = UnchartedCell::new(num_uncharted_cells);
        Self::new(mine_totals.iter().map(|(&num_mines, &k)| {
            (
                num_mines,
                Shared::new(FrontSubtally::from_data(
                    k,
                    [(Either::Right(meta_cell), num_mines as f64)].into_iter(),
                )),
            )
        }))
    }
}

type CollapseResult<T> = (Either<Rc<FrozenSet<Rc<T>>>, UnchartedCell>, f64);

#[derive(Clone, Debug, PartialEq)]
struct FrontSubtally<T: Cell> {
    total: f64,
    tally: HashMap<Either<Rc<FrozenSet<Rc<T>>>, UnchartedCell>, f64>,
    normalised: bool,
    finalised: bool,
}
impl<T: Cell> FrontSubtally<T> {
    pub fn new() -> Self {
        Self {
            total: 0.0,
            tally: HashMap::new(),
            normalised: false,
            finalised: false,
        }
    }

    pub fn add(&mut self, config: &Permutation<T>) {
        let mult = config.multiplicity() as f64;
        self.total += mult;
        for (super_cell, &n) in config.mapping.iter() {
            *self
                .tally
                .entry(Either::Left(Rc::clone(super_cell)))
                .or_insert(0.0) += n as f64 * mult;
        }
    }

    pub fn finalise(&mut self) {
        self.tally.values_mut().for_each(|n| *n /= self.total);
        self.finalised = true;
    }

    pub fn collapse(&self) -> impl Iterator<Item = CollapseResult<T>> + '_ {
        self.tally.iter().map(|(super_cell, &expected_mines)| {
            (super_cell.clone(), self.total * expected_mines)
        })
    }

    pub fn from_data(
        total: f64,
        tally: impl Iterator<Item = CollapseResult<T>>,
    ) -> Self {
        Self {
            total,
            tally: tally.collect(),
            normalised: false,
            finalised: true,
        }
    }
}

fn enumerate_front<T: Cell>(front: PermutedRuleset<T>) -> Result<FrontTally<T>, Error> {
    let mut tally = FrontTally::new(empty());
    tally.tally(front)?;
    Ok(tally)
}

fn cell_probabilities<'a, T: Cell + 'a>(
    tallies: Vec<Shared<FrontTally<T>>>,
    mine_prevalence: Either<BoardInfo, f64>,
    all_cells: Vec<Rc<FrozenSet<Rc<T>>>>,
) -> Result<impl Iterator<Item = CollapseResult<T>> + 'a, Error> {
    struct Iter<
        T: Cell,
        I: Iterator<Item = CollapseResult<T>>,
        J: Iterator<Item = CollapseResult<T>>,
    > {
        inner: Either<I, J>,
    }
    impl<
            T: Cell,
            I: Iterator<Item = CollapseResult<T>>,
            J: Iterator<Item = CollapseResult<T>>,
        > Iterator for Iter<T, I, J>
    {
        type Item = CollapseResult<T>;

        fn next(&mut self) -> Option<Self::Item> {
            match &mut self.inner {
                Either::Left(iter) => iter.next(),
                Either::Right(iter) => iter.next(),
            }
        }
    }
    Ok(
        weight_subtallies(tallies, mine_prevalence, all_cells)?.flat_map(|tally| {
            Iter {
                inner: match tally {
                    Either::Left(tally) => {
                        Either::Left(tally.borrow_mut().collapse().into_iter())
                    },
                    Either::Right(tally) => Either::Right(tally.collapse()),
                },
            }
        }),
    )
}

fn weight_subtallies<'a, T: Cell + 'a>(
    tallies: Vec<Shared<FrontTally<T>>>,
    mine_prevalence: Either<BoardInfo, f64>,
    all_cells: Vec<Rc<FrozenSet<Rc<T>>>>,
) -> Result<
    Box<dyn Iterator<Item = Either<Shared<FrontTally<T>>, FixedProbTally>> + 'a>,
    Error,
> {
    let dyn_tallies = tallies
        .iter()
        .filter(|tally| !tally.borrow().is_static())
        .cloned()
        .collect_vec();

    Ok(match mine_prevalence {
        Either::Left(board_info) => {
            let num_uncharted_cells =
                check_count_consistency(&tallies, board_info, all_cells)?;

            let num_static_mines = tallies
                .iter()
                .filter(|tally| tally.borrow().is_static())
                .map(|tally| tally.borrow().max_mines())
                .sum::<usize>();
            let at_large_mines = board_info.total_mines - num_static_mines;

            let tally_uncharted = Shared::new(combine_fronts(
                dyn_tallies,
                num_uncharted_cells,
                at_large_mines,
            ));
            Box::new(
                tallies
                    .into_iter()
                    .chain(once(tally_uncharted))
                    .map(Either::Left),
            )
        },
        Either::Right(mine_probability) => {
            let tally_uncharted = weight_nondiscrete(dyn_tallies, mine_probability)?;
            Box::new(
                tallies
                    .into_iter()
                    .map(Either::Left)
                    .chain(once(Either::Right(tally_uncharted))),
            )
        },
    })
}

fn weight_nondiscrete<T: Cell>(
    dyn_tallies: Vec<Shared<FrontTally<T>>>,
    mine_probability: f64,
) -> Result<FixedProbTally, Error> {
    for tally in dyn_tallies.into_iter() {
        let min_mines = tally.borrow().min_mines() as f64;
        tally.borrow_mut().scale_weights(|num_mines| {
            nondiscrete_relative_likelihood(
                mine_probability,
                num_mines as f64,
                min_mines,
            )
        })?;
    }

    Ok(FixedProbTally::new(mine_probability))
}

fn check_count_consistency<T: Cell>(
    tallies: &[Shared<FrontTally<T>>],
    board_info: BoardInfo,
    all_cells: Vec<Rc<FrozenSet<Rc<T>>>>,
) -> Result<usize, Error> {
    let (min_possible_mines, max_possible_mines) = possible_mine_limits(tallies);
    let num_uncharted_cells = board_info.total_cells
        - all_cells
            .into_iter()
            .map(|super_cell| super_cell.len())
            .sum::<usize>();
    if min_possible_mines > board_info.total_mines {
        Err("Minimum possible number of mines exceeds supplied mine count")
    } else if board_info.total_mines > max_possible_mines + num_uncharted_cells {
        Err("Supplied mine count exceeds maximum possible number of mines")
    } else {
        Ok(num_uncharted_cells)
    }
}

fn combine_fronts<T: Cell>(
    tallies: Vec<Shared<FrontTally<T>>>,
    num_uncharted_cells: usize,
    at_large_mines: usize,
) -> FrontTally<T> {
    struct FrontPerMineTotals {
        totals: HashMap<usize, f64>,
    }
    impl FrontPerMineTotals {
        pub fn singleton(num_mines: usize, total: f64) -> Self {
            Self {
                totals: [(num_mines, total)].into(),
            }
        }

        pub fn total_count(&self) -> f64 {
            self.totals.values().sum::<f64>()
        }

        pub fn multiply(&self, n: f64) -> Self {
            Self {
                totals: self.totals.iter().map(|(&k, &v)| (k, v * n)).collect(),
            }
        }

        pub fn sum<'a>(front_totals: impl Iterator<Item = &'a Self>) -> Self {
            Self {
                totals: map_reduce(
                    front_totals,
                    |front_totals| front_totals.totals.iter().map(|(&k, &v)| (k, v)),
                    |vals| vals.into_iter().sum::<f64>(),
                ),
            }
        }
    }
    struct AllFrontsPerMineTotals {
        front_totals: Vec<FrontPerMineTotals>,
    }
    impl AllFrontsPerMineTotals {
        pub fn total_count(&self) -> f64 {
            self.front_totals
                .get(0)
                .map_or(1.0, |front_total| front_total.total_count())
        }

        pub fn null() -> Self {
            Self {
                front_totals: Vec::new(),
            }
        }

        pub fn singleton(num_mines: usize, total: f64) -> Self {
            Self {
                front_totals: vec![FrontPerMineTotals::singleton(num_mines, total)],
            }
        }

        pub fn join_with(&self, other: &Self) -> Self {
            Self {
                front_totals: self
                    .front_totals
                    .iter()
                    .map(|f| f.multiply(other.total_count()))
                    .chain(
                        other
                            .front_totals
                            .iter()
                            .map(|f| f.multiply(self.total_count())),
                    )
                    .collect(),
            }
        }

        pub fn sum(front_sets: &[Self]) -> Self {
            if front_sets.is_empty() {
                return Self::null();
            }
            Self {
                front_totals: {
                    let mut results = vec![];
                    for i in 0..front_sets
                        .iter()
                        .map(|set| set.front_totals.len())
                        .min()
                        .expect("Already validated that there is at least one element")
                    {
                        let mut el = vec![];
                        for front in front_sets {
                            el.push(&front.front_totals[i]);
                        }
                        results.push(FrontPerMineTotals::sum(el.into_iter()));
                    }
                    results
                },
            }
        }
    }

    struct CombinedFront {
        totals: HashMap<usize, AllFrontsPerMineTotals>,
    }
    impl CombinedFront {
        pub fn min_max_mines(&self) -> (usize, usize) {
            (
                self.totals
                    .keys()
                    .copied()
                    .min()
                    .expect("Called min_max_mines on an empty CombinedFront"),
                self.totals
                    .keys()
                    .copied()
                    .max()
                    .expect("Called min_max_mines on an empty CombinedFront"),
            )
        }

        pub fn null() -> Self {
            Self {
                totals: [(0, AllFrontsPerMineTotals::null())].into(),
            }
        }

        pub fn from_counts_per_num_mines(
            mines_with_count: impl Iterator<Item = (usize, f64)>,
        ) -> Self {
            Self {
                totals: mines_with_count
                    .map(|(num_mines, total)| {
                        (
                            num_mines,
                            AllFrontsPerMineTotals::singleton(num_mines, total),
                        )
                    })
                    .collect(),
            }
        }

        pub fn from_tally<T: Cell>(tally: &FrontTally<T>) -> Self {
            Self::from_counts_per_num_mines(
                tally
                    .iter()
                    .map(|(num_mines, subtally)| (num_mines, subtally.borrow().total)),
            )
        }

        pub fn for_other(
            min_mines: usize,
            max_mines: usize,
            relative_likelihood: impl Fn(usize) -> f64,
        ) -> Self {
            Self::from_counts_per_num_mines(
                (min_mines..=max_mines).map(|n| (n, relative_likelihood(n))),
            )
        }

        pub fn join_with(
            &self,
            other: &Self,
            min_remaining_mines: usize,
            max_remaining_mines: usize,
            at_large_mines: usize,
        ) -> Self {
            let cross_entry = |((a_num_mines, a_fronts), (b_num_mines, b_fronts)): (
                (&usize, &AllFrontsPerMineTotals),
                (&usize, &AllFrontsPerMineTotals),
            )| {
                let combined_mines = a_num_mines + b_num_mines;
                let min_mines_at_end = combined_mines + min_remaining_mines;
                let max_mines_at_end = combined_mines + max_remaining_mines;
                if min_mines_at_end > at_large_mines
                    || max_mines_at_end < at_large_mines
                {
                    None
                } else {
                    Some((combined_mines, a_fronts.join_with(b_fronts)))
                }
            };

            let cross_entries = self
                .totals
                .iter()
                .cartesian_product(other.totals.iter())
                .filter_map(cross_entry);

            let new_totals = map_reduce(cross_entries, once, |vals| {
                AllFrontsPerMineTotals::sum(&vals)
            });
            Self {
                totals: new_totals,
            }
        }

        pub fn collapse(self) -> impl Iterator<Item = HashMap<usize, f64>> {
            assert_eq!(self.totals.len(), 1);
            let item = peek(self.totals.into_iter());
            item.1.front_totals.into_iter().map(|e| e.totals)
        }
    }

    let (min_tallied_mines, max_tallied_mines) = possible_mine_limits(&tallies);
    let min_other_mines = at_large_mines.saturating_sub(max_tallied_mines);
    let max_other_mines = min(at_large_mines - min_tallied_mines, num_uncharted_cells);

    let relative_likelihood = |num_free_mines: usize| {
        discrete_relative_likelihood(
            num_uncharted_cells,
            num_free_mines,
            max_other_mines,
        )
        .expect(concat!(
            "num_free_mines and max_other_mines should always",
            " be <= num_uncharted_cells",
        ))
    };

    let all_fronts = tallies
        .iter()
        .map(|t| CombinedFront::from_tally(&t.borrow()))
        .chain(once(CombinedFront::for_other(
            min_other_mines,
            max_other_mines,
            relative_likelihood,
        )))
        .collect_vec();
    let (mut min_remaining_mines, mut max_remaining_mines) = {
        let (mins, maxs): (Vec<_>, Vec<_>) =
            all_fronts.iter().map(|f| f.min_max_mines()).unzip();
        (
            mins.into_iter().sum::<usize>(),
            maxs.into_iter().sum::<usize>(),
        )
    };
    let mut combined = CombinedFront::null();
    for f in all_fronts {
        let (front_min, front_max) = f.min_max_mines();
        min_remaining_mines -= front_min;
        max_remaining_mines -= front_max;
        combined = combined.join_with(
            &f,
            min_remaining_mines,
            max_remaining_mines,
            at_large_mines,
        );
    }

    let front_totals = combined.collapse().collect_vec();
    let (uncharted_total, front_totals) = front_totals
        .split_last()
        .expect("Should always get at least one total out of collapse");

    for (tally, front_total) in tallies.iter().zip(front_totals) {
        tally.borrow_mut().update_weights(front_total);
    }

    FrontTally::for_other(num_uncharted_cells, uncharted_total)
}

fn possible_mine_limits<T: Cell>(tallies: &[Shared<FrontTally<T>>]) -> (usize, usize) {
    tallies
        .iter()
        .map(|tally| {
            let tally = tally.borrow();
            (tally.min_mines(), tally.max_mines())
        })
        .fold((0, 0), |(min, max), (tmin, tmax)| (min + tmin, max + tmax))
}

fn nondiscrete_relative_likelihood(p: f64, k: f64, k0: f64) -> Result<f64, Error> {
    if (0.0..=1.0).contains(&p) {
        Ok((p / (1.0 - p)).powf(k - k0))
    } else {
        Err("p must be in [0, 1]")
    }
}

fn discrete_relative_likelihood(n: usize, k: usize, k0: usize) -> Result<f64, Error> {
    if k > n || k0 > n {
        Err("k, k0 must be in [0, n]")
    } else {
        Ok(fact_div(k0, k) * fact_div(n - k0, n - k))
    }
}

#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq, PartialOrd, Ord)]
struct UnchartedCell {
    size: usize,
}
impl UnchartedCell {
    pub fn new(size: usize) -> Self {
        Self {
            size,
        }
    }

    pub fn len(&self) -> usize {
        self.size
    }
}

struct FixedProbTally {
    p: f64,
}
impl FixedProbTally {
    pub fn new(p: f64) -> Self {
        Self {
            p,
        }
    }

    pub fn collapse<T: Cell>(&self) -> impl Iterator<Item = CollapseResult<T>> {
        once((Either::Right(UnchartedCell::new(1)), self.p))
    }
}

type ExpandResult<T> = (Rc<T>, f64);

fn expand_cells<T: Cell>(
    cell_probs: impl Iterator<Item = CollapseResult<T>>,
    other_tag: Rc<T>,
) -> impl Iterator<Item = (Rc<T>, f64)> {
    struct Iter<T: Hash + Eq, I: Iterator<Item = CollapseResult<T>>> {
        cell_probs: I,
        inner: Either<
            <HashSet<Rc<T>> as IntoIterator>::IntoIter,
            <Option<(Rc<T>, f64)> as IntoIterator>::IntoIter,
        >,
        p: f64,
        other_tag: Rc<T>,
    }
    impl<T: Hash + Eq, I: Iterator<Item = CollapseResult<T>>> Iterator for Iter<T, I> {
        type Item = ExpandResult<T>;

        fn next(&mut self) -> Option<Self::Item> {
            match self.inner {
                Either::Left(ref mut inner) => inner.next().map(|t| (t, self.p)),
                Either::Right(ref mut inner) => inner.next(),
            }
            .or_else(|| {
                let (super_cell, p) = self.cell_probs.next()?;
                self.p = p;
                self.inner = match super_cell {
                    Either::Left(cells) => Either::Left((*cells).clone().into_iter()),
                    Either::Right(uncharted) => {
                        Either::Right(
                            // Skip the "other" cell if there aren't any
                            if uncharted.len() != 0 {
                                Some((
                                    Rc::clone(&self.other_tag),
                                    self.p / (uncharted.len() as f64),
                                ))
                            } else {
                                None
                            }
                            .into_iter(),
                        )
                    },
                };
                self.next()
            })
        }
    }
    Iter {
        cell_probs,
        inner: Either::Right(None.into_iter()),
        p: 0.0,
        other_tag,
    }
}
