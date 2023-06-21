use std::cmp::Ordering;
use std::collections::{hash_set, BinaryHeap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::ops::{Generator, GeneratorState};
use std::pin::Pin;

use either::Either;
use frozenset::{Freeze, FrozenSet};
use itertools::Itertools;

use crate::internal_util::{choose, graph_traverse, map_reduce, peek, peek_set, pop};

/// The state of the game is logically inconsistent.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct InconsistencyError(pub &'static str);

/// Represents the board geometry for traditional minesweeper, where the board
/// has fixed dimensions and a fixed total number of mines.
#[derive(Debug, Clone, Copy, Hash, PartialEq, Eq)]
pub struct MineCount {
    /// Total number of cells on the board; all cells contained in rules + all
    /// 'uncharted' (unknown) cells.
    pub total_cells: usize,
    /// Total number of mines contained within all cells
    pub total_mines: usize,
}

/// A type that can be used to uniquely identify a cell on the board.
///
/// Automatically implemented for any eligible type.
pub trait Cell: Clone + Hash + Eq {}
impl<T: Clone + Hash + Eq> Cell for T {
}
/// Either information about the board, or the probability of any unknown cell
/// being a mine (if the total number of mines is not known).
///
/// You shouldn't need to construct this type directly - use [`MineCount`] or
/// [`f64`]
pub struct MinePrevalence(pub Either<MineCount, f64>);
impl From<MineCount> for MinePrevalence {
    fn from(count: MineCount) -> Self {
        Self(Either::Left(count))
    }
}
impl From<f64> for MinePrevalence {
    fn from(prob: f64) -> Self {
        Self(Either::Right(prob))
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/// A basic representation of an axiom from a minesweeper game; N mines
/// contained within a set of M cells.
///
/// Only used during the very early stages of the algorithm; quickly converted
/// into an [`InternalRule`]
pub struct Rule<T: Cell> {
    /// How many mines
    pub(crate) num_mines: usize,
    /// Which cells; each 'cell' is a unique identifying tag that represents
    /// that cell (any type implementing [`Cell`])
    pub(crate) cells: FrozenSet<T>,
}
impl<T: Cell> Rule<T> {
    pub fn new(num_mines: usize, cells: impl IntoIterator<Item = T>) -> Self {
        Self {
            num_mines,
            cells: cells.into_iter().collect(),
        }
    }

    pub fn condensed(
        &self,
        rule_supercells_map: &HashMap<Self, FrozenSet<FrozenSet<T>>>,
    ) -> Result<InternalRule<T>, InconsistencyError> {
        InternalRule::new(
            self.num_mines,
            rule_supercells_map.get(self).cloned().unwrap_or_default(),
            self.cells.len(),
        )
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/// Analogue of [`Rule`], but containing 'super-cells' (sets of 'ordinary' cells
/// which only ever appear together).
///
/// This is the main representation of a rule used by the algorithm.
pub struct InternalRule<T: Cell> {
    #[cfg(test)]
    pub num_mines: usize,
    #[cfg(not(test))]
    /// The total number of mines
    num_mines: usize,
    #[cfg(test)]
    pub num_cells: usize,
    #[cfg(not(test))]
    /// The total number of base cells
    num_cells: usize,
    #[cfg(test)]
    pub super_cells: FrozenSet<FrozenSet<T>>,
    #[cfg(not(test))]
    /// The set of super-cells; each supercell is a set of base cells
    super_cells: FrozenSet<FrozenSet<T>>,
}
impl<T: Cell> InternalRule<T> {
    pub fn new(
        num_mines: usize,
        super_cells: FrozenSet<FrozenSet<T>>,
        num_cells: usize,
    ) -> Result<Self, InconsistencyError> {
        if num_mines > num_cells {
            return Err(InconsistencyError("Rule with more mines than cells"));
        }
        Ok(Self {
            num_mines,
            num_cells,
            super_cells,
        })
    }

    /// If this rule is completely full or clear of mines, split into sub-rules
    /// for each super-cell
    pub fn decompose(self) -> Vec<Self> {
        if self.num_mines == 0 || self.num_mines == self.num_cells {
            // Degenerate rules (those containing no cells) disappear here
            self.super_cells
                .into_iter()
                .map(|cells| {
                    Self {
                        num_mines: if self.num_mines == 0 { 0 } else { cells.len() },
                        num_cells: cells.len(),
                        super_cells: [cells].into(),
                    }
                })
                .collect()
        } else {
            vec![self]
        }
    }

    /// Generate all possible mine permutations for this rule
    #[allow(clippy::needless_pass_by_value)]
    pub fn permute(&self) -> HashSet<Permutation<T>> {
        pub fn permute<T: Cell>(
            result: &mut HashSet<Permutation<T>>,
            count: usize,
            cells: &[FrozenSet<T>],
            in_progress: HashSet<(FrozenSet<T>, usize)>,
        ) {
            if count == 0 {
                result.insert(Permutation::new(
                    in_progress
                        .union(&cells.iter().map(|cell| (cell.clone(), 0)).collect())
                        .cloned()
                        .collect(),
                ));
            } else {
                let remaining_size = cells.iter().map(|cell| cell.len()).sum::<usize>();
                match remaining_size.cmp(&count) {
                    Ordering::Less => (),
                    Ordering::Equal => {
                        result.insert(Permutation::new(
                            in_progress
                                .union(
                                    &cells
                                        .iter()
                                        .map(|cell| (cell.clone(), cell.len()))
                                        .collect(),
                                )
                                .cloned()
                                .collect(),
                        ));
                    },
                    Ordering::Greater => {
                        let (cell, rest) = cells.split_first().expect(
                            "Must always have at least one element to reach this point",
                        );
                        for multiplicity in (0..=count.min(cell.len())).rev() {
                            permute(
                                result,
                                count - multiplicity,
                                rest,
                                in_progress
                                    .union(&[(cell.clone(), multiplicity)].into())
                                    .cloned()
                                    .collect(),
                            );
                        }
                    },
                }
            }
        }
        let mut result = HashSet::new();
        let cells = self.super_cells.iter().cloned().collect_vec();
        permute(&mut result, self.num_mines, &cells, HashSet::new());
        result
    }

    /// Check if this rule is a sub-rule of `other`
    ///
    /// Being a sub-rule means that this rule's cells are a subset of the other
    /// rule's cells. Equivalent rules are sub-rules of each other.
    pub fn is_subrule_of(&self, other: &Self) -> bool {
        self.super_cells.is_subset(&other.super_cells)
            && self.num_mines <= other.num_mines
    }

    /// If the other rule is a sub-rule of this one, return a new rule
    /// representing the difference between the two rules.
    pub fn subtract(&self, other: &Self) -> Result<Self, InconsistencyError> {
        if !other.is_subrule_of(self) {
            return Err(InconsistencyError("Subtraction of non-subrule"));
        }
        let super_cells = self
            .super_cells
            .difference(&other.super_cells)
            .cloned()
            .collect();
        Self::new(
            self.num_mines - other.num_mines,
            super_cells,
            self.num_cells - other.num_cells,
        )
    }

    /// Is this rule trivial (i.e. is there only one permutation)?
    pub fn is_trivial(&self) -> bool {
        self.super_cells.len() == 1
    }

    /// Build a `FrontTally` from this (trivial) rule
    pub fn tally(&self) -> FrontTally<T> {
        assert!(self.is_trivial());
        FrontTally::from_rule(self)
    }

    pub fn new_count_cells(
        num_mines: usize,
        super_cells: FrozenSet<FrozenSet<T>>,
    ) -> Result<Self, InconsistencyError> {
        let num_cells = super_cells.iter().map(|s| s.len()).sum();
        Self::new(num_mines, super_cells, num_cells)
    }

    #[cfg(test)]
    /// Helper method for testing
    pub fn from_data(
        num_mines: usize,
        super_cells: impl Iterator<Item = impl Iterator<Item = T>>,
    ) -> Result<Self, InconsistencyError> {
        Self::new_count_cells(
            num_mines,
            super_cells.map(Iterator::collect).collect::<FrozenSet<_>>(),
        )
    }
}

#[derive(Debug, Clone)]
/// Tabulation of per-cell mine frequencies
pub struct FrontTally<T: Cell> {
    /// Number of mines in configuration -> subtally of configurations with that
    /// many mines
    pub(crate) subtallies: HashMap<usize, FrontSubtally<T>>,
}
impl<T: Cell> FrontTally<T> {
    pub fn new() -> Self {
        Self {
            subtallies: HashMap::new(),
        }
    }

    pub fn new_with_data(subtallies: HashMap<usize, FrontSubtally<T>>) -> Self {
        Self {
            subtallies,
        }
    }

    /// Tally all possible configurations for a front (ruleset)
    ///
    /// Note that the tallies for different total numbers of mines must be
    /// maintained separately, as these will be given different statistical
    /// weights later on.
    pub fn tally(
        &mut self,
        front: &PermutedRuleset<T>,
    ) -> Result<(), InconsistencyError> {
        for config in front.enumerate() {
            self.subtallies
                .entry(config.k())
                .or_insert_with(FrontSubtally::new)
                .add(&config);
        }

        if self.subtallies.is_empty() {
            return Err(InconsistencyError(
                "Mine front has no possible configurations",
            ));
        }

        self.finalise();
        Ok(())
    }

    /// Finalise all sub-tallies (convert running totals to
    /// probabilities/expected values)
    pub fn finalise(&mut self) {
        for subtally in self.subtallies.values_mut() {
            subtally.finalise();
        }
    }

    /// Minimum number of mines found among all configurations
    pub fn min_mines(&self) -> usize {
        self.subtallies
            .keys()
            .copied()
            .min()
            .expect("Should always have at least one sub-tally")
    }

    /// Maximum number of mines found among all configurations
    pub fn max_mines(&self) -> usize {
        self.subtallies
            .keys()
            .copied()
            .max()
            .expect("Should always have at least one sub-tally")
    }

    /// Whether all configurations have the same number of mines (simplifies
    /// statistical weighting later)
    pub fn is_static(&self) -> bool {
        self.subtallies.len() == 1
    }

    /// Normalise sub-tally totals into relative weights such that sub-totals
    /// remain proportional to each other, and the grand total across all
    /// sub-tallies is 1
    pub fn normalise(&mut self) {
        let total = self
            .subtallies
            .values()
            .map(|subtally| subtally.total)
            .sum::<f64>();
        for subtally in self.subtallies.values_mut() {
            assert!(!subtally.normalised, "Sub-tally already normalised");
            subtally.total /= total;
            subtally.normalised = true;
        }
    }

    /// Calculate the per-cell expected mine values, summed and weighted across
    /// all sub-tallies
    pub fn collapse(mut self) -> HashMap<Either<FrozenSet<T>, UnchartedCell>, f64> {
        self.normalise();
        map_reduce(self.subtallies.values(), FrontSubtally::collapse, |data| {
            data.into_iter().sum::<f64>()
        })
    }

    /// Scale each sub-tally's weight/total according to `scale_fn`
    pub fn scale_weights(
        &mut self,
        scale_fn: impl Fn(usize) -> Result<f64, InconsistencyError>,
    ) -> Result<(), InconsistencyError> {
        for (&num_mines, subtally) in &mut self.subtallies {
            subtally.total *= scale_fn(num_mines)?;
        }
        Ok(())
    }

    /// Update each sub-tally's weight/total according to `weights`
    ///
    /// `weights`: `num_mines` -> new weight of the sub-tally for `num_mines`
    pub fn update_weights(&mut self, weights: &HashMap<usize, f64>) {
        for (num_mines, subtally) in &mut self.subtallies {
            subtally.total = weights.get(num_mines).copied().unwrap_or(0.0);
        }
    }

    /// Tally a trivial rule
    pub fn from_rule(rule: &InternalRule<T>) -> Self {
        assert!(rule.is_trivial());
        #[allow(clippy::cast_precision_loss)]
        Self::new_with_data(
            [(
                rule.num_mines,
                FrontSubtally::from_data(
                    choose(rule.num_cells, rule.num_mines) as f64,
                    [(
                        Either::Left(
                            peek_set(&rule.super_cells).expect(
                                "Should always contain at least one super-cell",
                            ),
                        ),
                        rule.num_mines as f64,
                    )]
                    .into(),
                ),
            )]
            .into(),
        )
    }

    /// Create a meta-tally representing the mine distribution of all 'other'
    /// cells.
    ///
    /// - `num_uncharted_cells`: The number of 'other' cells
    /// - `mine_totals`: A mapping suitable for `update_weights`; `num_mines` ->
    ///   new weight of the sub-tally for `num_mines`
    #[allow(clippy::cast_precision_loss)]
    pub fn for_other(
        num_uncharted_cells: usize,
        mine_totals: &HashMap<usize, f64>,
    ) -> Self {
        let meta_cell = UnchartedCell::new(num_uncharted_cells);
        Self::new_with_data(
            mine_totals
                .iter()
                .map(|(&num_mines, &total)| {
                    (
                        num_mines,
                        FrontSubtally::from_data(
                            total,
                            [(Either::Right(meta_cell), num_mines as f64)].into(),
                        ),
                    )
                })
                .collect(),
        )
    }
}

impl<T: Cell> Default for FrontTally<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone)]
/// Sub-tabulation of per-cell mine frequencies
pub struct FrontSubtally<T: Cell> {
    /// 'weight' of this sub-tally among the others in the [`FrontTally`].
    /// Initially will be a raw count of the configurations in this sub-tally,
    /// but later will be skewed due to weighting and normalising factors.
    pub(crate) total: f64,
    /// # Pre-finalising
    ///
    /// Per-cell mine counts
    ///
    /// Super-cell -> total number of mines in the super-cell, summed across all
    /// configurations
    ///
    /// # Post-finalising
    ///
    /// Mine prevalence
    ///
    /// Super-cell -> Expected number of mines in the super-cell
    tally: HashMap<Either<FrozenSet<T>, UnchartedCell>, f64>,
    finalised: bool,
    normalised: bool,
}
impl<T: Cell> FrontSubtally<T> {
    pub fn new() -> Self {
        Self {
            total: 0.0,
            tally: HashMap::new(),
            finalised: false,
            normalised: false,
        }
    }

    /// Add a configuration to the tally
    #[allow(clippy::cast_precision_loss)]
    pub fn add(&mut self, config: &Permutation<T>) {
        let mult = config.multiplicity() as f64; // Weight by multiplicity
        self.total += mult;
        for (super_cell, &n) in &config.mapping {
            let n = n as f64;
            self.tally
                .entry(Either::Left(super_cell.clone()))
                .and_modify(|tally| *tally += n * mult)
                .or_insert(n * mult);
        }
    }

    /// After all configurations have been summed, compute relative prevalence
    /// from totals.
    pub fn finalise(&mut self) {
        for value in self.tally.values_mut() {
            *value /= self.total;
        }
        self.finalised = true;
    }

    /// Helper function for [`FrontTally::collapse()`]; emit all cell expected
    /// mine values weighted by this sub-tally's weight
    pub fn collapse(
        &self,
    ) -> impl Iterator<Item = (Either<FrozenSet<T>, UnchartedCell>, f64)> + '_ {
        self.tally.iter().map(|(super_cell, &expected_mines)| {
            (super_cell.clone(), self.total * expected_mines)
        })
    }

    /// Build a sub-tally manually. Tally data must already be finalised.
    pub fn from_data(
        total: f64,
        tally: HashMap<Either<FrozenSet<T>, UnchartedCell>, f64>,
    ) -> Self {
        Self {
            total,
            tally,
            finalised: true,
            normalised: false,
        }
    }
}

impl<T: Cell> Default for FrontSubtally<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
/// A meta-cell object that represents all the 'other' cells on the board, that
/// aren't explicitly mentioned in a rule. See [`expand_cells()`].
pub struct UnchartedCell {
    size: usize,
}
impl UnchartedCell {
    pub fn new(size: usize) -> Self {
        Self {
            size,
        }
    }

    /// Only appear once in the solution, regardless of size. However, don't
    /// appear at all if there are in fact no 'other' cells
    pub fn iter(self) -> impl Iterator<Item = ()> {
        if self.size == 0 {
            None.into_iter()
        } else {
            Some(()).into_iter()
        }
    }

    pub fn len(self) -> usize {
        self.size
    }

    pub fn is_empty(self) -> bool {
        self.len() == 0
    }
}

/// A meta-tally to represent when all 'other' cells are uncounted and assumed
/// to have a fixed mine probability
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct FixedProbTally(pub(crate) f64);
impl FixedProbTally {
    pub fn collapse<T: Cell>(
        self,
    ) -> HashMap<Either<FrozenSet<T>, UnchartedCell>, f64> {
        [(Either::Right(UnchartedCell::new(1)), self.0)].into()
    }
}
impl Eq for FixedProbTally {
}
impl Hash for FixedProbTally {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.0.to_bits().hash(state);
    }
}

#[derive(Debug, Clone)]
/// Manager object that performs the 'logical deduction' phase of the solver;
/// maintains a set of active rules, tracks which rules overlap with other
/// rules, and iteratively reduces them until no further reductions are possible
pub struct RuleReducer<T: Cell> {
    active_rules: HashSet<InternalRule<T>>,
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

    /// Add a set of rules to the ruleset
    pub fn add_rules(
        &mut self,
        rules: impl Iterator<Item = InternalRule<T>>,
    ) -> Result<(), InconsistencyError> {
        for rule in rules {
            self.add_rule(rule)?;
        }
        Ok(())
    }

    /// Add a new rule to the active ruleset
    pub fn add_rule(
        &mut self,
        rule: InternalRule<T>,
    ) -> Result<(), InconsistencyError> {
        for base_rule in rule.decompose() {
            self.add_base_rule(base_rule)?;
        }
        Ok(())
    }

    /// Helper for adding a rule
    pub fn add_base_rule(
        &mut self,
        rule: InternalRule<T>,
    ) -> Result<(), InconsistencyError> {
        self.active_rules.insert(rule.clone());
        self.update_reduceables(&rule)?;
        self.cell_rules_map.add_rule(rule);
        Ok(())
    }

    pub fn add_reduceable(&mut self, reduceable: Reduceable<T>) {
        self.candidate_reductions.push(reduceable);
    }

    /// Update the index of which rules are reduceable from others
    pub fn update_reduceables(
        &mut self,
        rule: &InternalRule<T>,
    ) -> Result<(), InconsistencyError> {
        let overlapping = self.cell_rules_map.overlapping_rules(rule);
        for overlapping_rule in overlapping {
            if overlapping_rule.is_subrule_of(rule) {
                // This path is taken if the rules are equivalent
                self.add_reduceable(Reduceable::new(rule.clone(), overlapping_rule)?);
            } else if rule.is_subrule_of(&overlapping_rule) {
                // This path is taken if the overlapping rule is a subrule of
                // the new rule
                self.add_reduceable(Reduceable::new(overlapping_rule, rule.clone())?);
            }
        }
        Ok(())
    }

    /// Remove a rule from the active ruleset/index, presumably because it has
    /// been reduced away
    pub fn remove_rule(&mut self, rule: &InternalRule<T>) {
        self.active_rules.remove(rule);
        self.cell_rules_map.remove_rule(rule);
        // We can't remove the inner contents of candidate_reductions; instead,
        // items are checked for validity when they are popped off the heap
    }

    /// Perform a reduction
    pub fn reduce(
        &mut self,
        reduction: &Reduceable<T>,
    ) -> Result<(), InconsistencyError> {
        let reduced_rule = reduction.reduce()?;
        self.remove_rule(&reduction.super_rule);
        self.add_rule(reduced_rule)
    }

    /// Perform reductions until no further reductions are possible
    pub fn reduce_all(
        mut self,
    ) -> Result<HashSet<InternalRule<T>>, InconsistencyError> {
        while let Some(reduction) = self.candidate_reductions.pop() {
            if !reduction.contained_within(&self.active_rules) {
                continue;
            }
            self.reduce(&reduction)?;
        }
        Ok(self.active_rules)
    }
}

#[derive(Debug, Clone)]
/// A utility struct mapping cells to the rules they appear in
pub struct CellRulesMap<T: Cell> {
    /// Super-cell -> Set of rules containing that super-cell
    map: HashMap<FrozenSet<T>, HashSet<InternalRule<T>>>,
    rules: HashSet<InternalRule<T>>,
}
impl<T: Cell> CellRulesMap<T> {
    pub fn new() -> Self {
        Self {
            map: HashMap::new(),
            rules: HashSet::new(),
        }
    }

    pub fn add_rules(&mut self, rules: impl Iterator<Item = InternalRule<T>>) {
        for rule in rules {
            self.add_rule(rule);
        }
    }

    pub fn add_rule(&mut self, rule: InternalRule<T>) {
        for super_cell in rule.super_cells.iter() {
            self.map
                .entry(super_cell.clone())
                .or_default()
                .insert(rule.clone());
        }
        self.rules.insert(rule);
    }

    pub fn remove_rule(&mut self, rule: &InternalRule<T>) {
        self.rules.remove(rule);
        for super_cell in rule.super_cells.iter() {
            if let Some(set) = self.map.get_mut(super_cell) {
                set.remove(rule);
            }
        }
    }

    /// Return the set of rules that overlap `rule`, i.e. that have at least one
    /// cell in common
    pub fn overlapping_rules(
        &self,
        rule: &InternalRule<T>,
    ) -> HashSet<InternalRule<T>> {
        let mut res: HashSet<_> = rule
            .super_cells
            .iter()
            .flat_map(|cell| self.map.get(cell).cloned().unwrap_or_default())
            .collect();
        res.remove(rule);
        res
    }

    /// Return pairs of all rules that overlap each other; each pair is
    /// represented twice (`(a, b)` and `(b, a)`) to support processing of
    /// asymmetric relationships
    pub fn interference_edges(&self) -> HashSet<(InternalRule<T>, InternalRule<T>)> {
        self.rules
            .iter()
            .flat_map(|rule| {
                self.overlapping_rules(rule)
                    .into_iter()
                    .map(|other| (rule.clone(), other))
            })
            .collect()
    }

    /// Partition the ruleset into disjoin sub-rulesets of related rules.
    ///
    /// That is, all rules in a sub-ruleset are related to each other in some
    /// way through some number of overlaps, and no rules from separate
    /// sub-rulesets overlap each other. Returns a set of partitions, each a set
    /// of rules.
    pub fn partition(&self) -> HashSet<FrozenSet<InternalRule<T>>> {
        let mut related_rules = self
            .rules
            .iter()
            .map(|rule| (rule.clone(), self.overlapping_rules(rule)))
            .collect::<HashMap<_, _>>();
        let mut partitions = HashSet::new();
        while let Some(start) = peek(&related_rules) {
            let partition = graph_traverse(&related_rules, &start);
            for rule in &partition {
                related_rules.remove(rule);
            }
            partitions.insert(partition.freeze());
        }
        partitions
    }
}

#[derive(Debug, Clone, Hash, PartialEq, Eq)]
/// During the logical deduction phase; if all rules are nodes in a graph, this
/// represents a directed edge in that graph indicating that `super_rule` can be
/// reduced by `sub_rule`
pub struct Reduceable<T: Cell> {
    super_rule: InternalRule<T>,
    sub_rule: InternalRule<T>,
}
impl<T: Cell> Reduceable<T> {
    pub fn new(
        super_rule: InternalRule<T>,
        sub_rule: InternalRule<T>,
    ) -> Result<Self, InconsistencyError> {
        if false {
            return Err(InconsistencyError("shut up clippy"));
        }
        // if !sub_rule.is_subrule_of(&super_rule) {
        //     return Err(InconsistencyError(
        //         "`sub_rule` is not a sub-rule of `super_rule`",
        //     ));
        // }
        Ok(Self {
            super_rule,
            sub_rule,
        })
    }

    /// Calculate the attractiveness of this reduction.
    ///
    /// Favour reductions that involve bigger rules, and amongst same-sized
    /// rules, those that yield a number of mines towards the extremes; such
    /// rules have fewer permutations
    pub fn metric(&self) -> (usize, usize, f64) {
        let num_reduced_cells = self.super_rule.num_cells - self.sub_rule.num_cells;
        let num_reduced_mines = self.super_rule.num_mines - self.sub_rule.num_mines;
        #[allow(clippy::cast_precision_loss)]
        (
            self.super_rule.num_cells,
            self.sub_rule.num_cells,
            (num_reduced_mines as f64 - 0.5 * num_reduced_cells as f64).abs(),
        )
    }

    /// Perform the reduction
    pub fn reduce(&self) -> Result<InternalRule<T>, InconsistencyError> {
        self.super_rule.subtract(&self.sub_rule)
    }

    pub fn contained_within(&self, rules: &HashSet<InternalRule<T>>) -> bool {
        rules.contains(&self.super_rule) && rules.contains(&self.sub_rule)
    }
}
impl<T: Cell> PartialOrd for Reduceable<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.metric().partial_cmp(&other.metric())
    }
}
impl<T: Cell> Ord for Reduceable<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        self.partial_cmp(other).unwrap()
    }
}

/// A set of rules and the available permutations for each, eliminating
/// permutations which are mutually-inconsistent across the ruleset
#[derive(Debug, Clone)]
pub struct PermutedRuleset<T: Cell> {
    rules: HashSet<InternalRule<T>>,
    cell_rules_map: CellRulesMap<T>,
    #[cfg(test)]
    pub permu_map: HashMap<InternalRule<T>, PermutationSet<T>>,
    #[cfg(not(test))]
    permu_map: HashMap<InternalRule<T>, PermutationSet<T>>,
}
impl<T: Cell> PermutedRuleset<T> {
    pub fn new_with_permu_map(
        rules: HashSet<InternalRule<T>>,
        permu_map: HashMap<InternalRule<T>, PermutationSet<T>>,
    ) -> Self {
        let mut cell_rules_map = CellRulesMap::new();
        cell_rules_map.add_rules(rules.iter().cloned());
        Self {
            rules,
            cell_rules_map,
            permu_map,
        }
    }

    pub fn new(rules: HashSet<InternalRule<T>>) -> Self {
        let permu_map = rules
            .iter()
            .map(|rule| (rule.clone(), PermutationSet::from_rule(rule)))
            .collect();
        Self::new_with_permu_map(rules, permu_map)
    }

    pub fn new_as_subset(
        rules: HashSet<InternalRule<T>>,
        permu_map: &HashMap<InternalRule<T>, PermutationSet<T>>,
    ) -> Self {
        let permu_map = rules
            .iter()
            .map(|rule| (rule.clone(), permu_map[rule].clone()))
            .collect();
        Self::new_with_permu_map(rules, permu_map)
    }

    /// Determine what permutations are possible for each rule, taking into
    /// account the constraints of all overlapping rules. Eliminate impossible
    /// permutations
    pub fn cross_eliminate(&mut self) -> Result<(), InconsistencyError> {
        let mut interferences = self.cell_rules_map.interference_edges();

        // We can't simply iterate through `interferences`, as eliminating a permutation
        // in a rule may in turn invalidate permutations in other overlapping rules that
        // have already been processed, thus causing a cascade effect.
        while let Some((rule, overlapping)) = pop(&mut interferences) {
            let mut changed = false;
            // Copy the iterable so we can modify the original
            for permutation in self.permu_map[&rule].permutations.clone() {
                if self.permu_map[&overlapping]
                    .get_compatible(&permutation)
                    .is_empty()
                {
                    // This permutation has no compatible permutation in the overlapping
                    // rule. Thus, it can never occur.
                    self.permu_map
                        .get_mut(&rule)
                        .expect("Definitely exists, as we have already used it")
                        .remove(&permutation);
                    changed = true;
                }
            }

            if self.permu_map[&rule].is_empty() {
                // We have eliminated all possible configurations for this rule.
                return Err(InconsistencyError(
                    "Rule is constrained such that it has no valid mine permutations",
                ));
            } else if changed {
                for other_rule in self.cell_rules_map.overlapping_rules(&rule) {
                    interferences.insert((other_rule, rule.clone()));
                }
            }
        }
        Ok(())
    }

    /// After computing the possible permutations of the rules, analyse and
    /// decompose rules into sub-rules, if possible. This can eliminate
    /// dependencies among the initial set of rules, and thus potentially split
    /// what would have been one rule-front into several.
    ///
    /// This is analogous to the previous `reduce_rules` step, but with more
    /// advanced logical analysis -- exploiting information gleaned from the
    /// permutation phase
    pub fn rereduce(&mut self) -> Result<(), InconsistencyError> {
        // Convincing conjectures:
        // - Among all cartesian decompositions from all rules, none will be reduceable
        //   with another (decomposed rules may have duplicates, though)
        // - Cartesian decomposition will have effectively re-reduced all rules in the
        //   set, even non-decomposed rules; there will be no possible reductions
        //   between a decomposed rule and an original rule
        // - Re-permuting amongs the decomposed ruleset will produce the same
        //   permutation sets

        let mut superseded_rules = HashSet::new();
        let mut decompositions = HashMap::new();
        for (rule, permu_set) in &self.permu_map {
            let decomp = permu_set.clone().decompose();
            if decomp.len() > 1 {
                superseded_rules.insert(rule.clone());
                decompositions.extend(
                    decomp.iter().map(|dc| (dc.super_cells.clone(), dc.clone())),
                );
            }
        }

        for rule in &superseded_rules {
            self.remove_rule(rule);
        }
        for permu_set in decompositions.into_values() {
            self.add_permu_set(permu_set)?;
        }
        Ok(())
    }

    pub fn remove_rule(&mut self, rule: &InternalRule<T>) {
        self.rules.remove(rule);
        self.cell_rules_map.remove_rule(rule);
        self.permu_map.remove(rule);
    }

    /// Add a 'decomposed' rule to the ruleset
    pub fn add_permu_set(
        &mut self,
        permu_set: PermutationSet<T>,
    ) -> Result<(), InconsistencyError> {
        let rule = permu_set.to_rule()?;
        self.rules.insert(rule.clone());
        self.cell_rules_map.add_rule(rule.clone());
        self.permu_map.insert(rule, permu_set);
        Ok(())
    }

    /// Return a [`PermutedRuleset`] built from this one containing only a
    /// subset of rules
    pub fn filter(&self, rule_subset: HashSet<InternalRule<T>>) -> Self {
        Self::new_as_subset(rule_subset, &self.permu_map)
    }

    /// Split the ruleset into combinatorially-independent 'fronts'
    pub fn split_fronts(&self) -> Vec<Self> {
        self.cell_rules_map
            .partition()
            .into_iter()
            .map(|rule_subset| self.filter(rule_subset.thaw()))
            .collect()
    }

    /// Is this ruleset trivial? I.E. does it contain only one rule?
    pub fn is_trivial(&self) -> bool {
        self.rules.len() == 1
    }

    /// Return the singleton rule of this ruleset, if it is trivial
    pub fn trivial_rule(&self) -> InternalRule<T> {
        assert!(self.is_trivial());
        let singleton = self.rules.iter().next().unwrap().clone();
        assert!(singleton.is_trivial());
        singleton
    }

    /// Enumerate all possible mine configurations for this ruleset
    pub fn enumerate(&self) -> impl Iterator<Item = Permutation<T>> + '_ {
        EnumerationState::new(self).enumerate()
    }
}

#[derive(Debug, Clone)]
pub struct EnumerationState<'a, T: Cell> {
    fixed: HashSet<Permutation<T>>,
    ruleset: &'a PermutedRuleset<T>,
    free: HashMap<InternalRule<T>, HashSet<Permutation<T>>>,
    compatible_rule_index:
        HashMap<(Permutation<T>, InternalRule<T>), PermutationSet<T>>,
}
impl<'a, T: Cell> EnumerationState<'a, T> {
    pub fn new(ruleset: &'a PermutedRuleset<T>) -> Self {
        let mut rv = Self {
            fixed: HashSet::new(),
            ruleset,
            free: ruleset
                .permu_map
                .iter()
                .map(|(rule, permu_set)| (rule.clone(), permu_set.permutations.clone()))
                .collect(),
            compatible_rule_index: HashMap::new(),
        };
        rv.build_compatibility_index();
        rv
    }

    /// Passes through to `self.ruleset.overlapping_rules`
    pub fn overlapping_rules(
        &self,
        rule: &InternalRule<T>,
    ) -> HashSet<InternalRule<T>> {
        self.ruleset.cell_rules_map.overlapping_rules(rule)
    }

    /// Compute the `compatible_rule_index` for this ruleset
    pub fn build_compatibility_index(&mut self) {
        let map = &self.ruleset.permu_map;
        self.compatible_rule_index = map
            .iter()
            .flat_map(|(rule, permu_set)| {
                permu_set.permutations.iter().flat_map(|permu| {
                    self.overlapping_rules(rule).into_iter().map(|overlapping| {
                        let compatible = map[&overlapping].get_compatible(permu);
                        ((permu.clone(), overlapping), compatible)
                    })
                })
            })
            .collect();
    }

    /// Have all rules been fixed? I.E. is the configuration complete?
    pub fn is_complete(&self) -> bool {
        self.free.is_empty()
    }

    /// 'Fix' a permutation for a given rule
    pub fn propagate(
        &self,
        rule: &InternalRule<T>,
        permu: &Permutation<T>,
    ) -> Option<Self> {
        let mut state = self.clone();
        state.force_propagate(rule, permu)?;
        Some(state)
    }

    /// 'Fix' a rule permutation and constrain the available permutations of all
    /// overlapping rules
    pub fn force_propagate(
        &mut self,
        rule: &InternalRule<T>,
        permu: &Permutation<T>,
    ) -> Option<()> {
        self.fixed.insert(permu.clone());
        self.free.remove(rule);

        // Constrain overlapping rules
        let mut cascades = Vec::new();
        for related_rule in self
            .overlapping_rules(rule)
            .into_iter()
            .filter(|rule| self.free.contains_key(rule))
            .collect_vec()
        // clone the iterator to avoid borrowing issues
        {
            // PermutationSet of the related rule, constrained *only* by the
            // rule/permutation just fixed
            let allowed_permus = self.compatible_rule_index
                [&(permu.clone(), related_rule.clone())]
                .clone();
            // Further constrain the related rule with this new set -- is now properly
            // constrained by all fixed rules
            self.free
                .get_mut(&related_rule)
                .unwrap()
                .retain(|permu| allowed_permus.permutations.contains(permu));

            let linked_permus = &self.free[&related_rule];
            if linked_permus.is_empty() {
                // conflict!
                return None;
            } else if linked_permus.len() == 1 {
                // only one possibility; constrain further
                cascades.push((
                    related_rule.clone(),
                    linked_permus.iter().next().unwrap().clone(),
                ));
            }
        }

        // Cascade if any other rules are not fully constrained
        for (related_rule, constrained_permu) in cascades {
            // May have already been constrained by prior recursive call
            if self.free.contains_key(&related_rule) {
                self.force_propagate(&related_rule, &constrained_permu)?;
            }
        }
        Some(())
    }

    /// Convert the set of fixed permutations into a single Permutation
    /// encompassing the mine configuration for the entire ruleset
    pub fn mine_config(&self) -> Option<Permutation<T>> {
        let mut iter = self.fixed.iter();
        let first = iter.next()?;
        Some(iter.fold(first.clone(), |acc, elem| acc.combine(elem)))
    }

    /// Recursively generate all possible mine configurations for the ruleset
    pub fn enumerate(self) -> impl Iterator<Item = Permutation<T>> + 'a {
        EnumerationStateEnumerate::new(self)
    }

    pub fn iter(&self) -> impl Iterator<Item = EnumerationState<'_, T>> + '_ {
        EnumerationStateIter::new(self)
    }
}

/// Pick an 'open' rule at random and 'fix' each possible permutation for that
/// rule. In this manner, when done recursively, all valid combinations are
/// enumerated.
#[derive(Debug, Clone)]
pub struct EnumerationStateIter<'a, T: Cell> {
    rule: InternalRule<T>,
    free_iter: hash_set::Iter<'a, Permutation<T>>,
    state: &'a EnumerationState<'a, T>,
}
impl<'a, T: Cell> EnumerationStateIter<'a, T> {
    pub fn new(state: &'a EnumerationState<'a, T>) -> Self {
        let rule = peek(&state.free).unwrap();
        Self {
            free_iter: state.free[&rule].iter(),
            rule,
            state,
        }
    }
}
impl<'a, T: Cell> Iterator for EnumerationStateIter<'a, T> {
    type Item = EnumerationState<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        let permu = self.free_iter.next()?;
        self.state
            .propagate(&self.rule, permu)
            .or_else(|| self.next())
    }
}

/// Recursively generate all possible mine configurations for the ruleset
pub struct EnumerationStateEnumerate<'a, T: Cell> {
    inner: Pin<Box<dyn Generator<Yield = Permutation<T>, Return = ()> + 'a>>,
}
impl<'a, T: Cell> EnumerationStateEnumerate<'a, T> {
    pub fn new(state: EnumerationState<'a, T>) -> Self {
        Self {
            inner: Box::pin(static move || {
                if state.is_complete() {
                    yield state.mine_config().expect(
                        "Mine configuration should always be valid when \
                         state.is_complete()",
                    );
                } else {
                    let states = state.iter().collect_vec();
                    for next_state in states {
                        for val in next_state.enumerate() {
                            yield val;
                        }
                    }
                }
            }),
        }
    }
}

impl<T: Cell> Iterator for EnumerationStateEnumerate<'_, T> {
    type Item = Permutation<T>;

    fn next(&mut self) -> Option<Self::Item> {
        match self.inner.as_mut().resume(()) {
            GeneratorState::Yielded(val) => Some(val),
            GeneratorState::Complete(()) => None,
        }
    }
}

/// A set of permutations of the same cell set and total number of mines.
///
/// May be the full set of possible permutations, or a subset as particular
/// permutations are removed due to outside conflicts
#[derive(Debug, Clone)]
pub struct PermutationSet<T: Cell> {
    super_cells: FrozenSet<FrozenSet<T>>,
    k: usize,
    #[cfg(test)]
    pub(crate) permutations: HashSet<Permutation<T>>,
    #[cfg(not(test))]
    permutations: HashSet<Permutation<T>>,
    /// `false` if the set is the full set of possible permutations; `true` if
    /// the set has since been reduced. Accurate iff the `PermutationSet` was
    /// created with the full set of possibilities.
    constrained: bool,
}
impl<T: Cell> PermutationSet<T> {
    pub fn new(
        super_cells: FrozenSet<FrozenSet<T>>,
        k: usize,
        permutations: HashSet<Permutation<T>>,
    ) -> Self {
        Self {
            super_cells,
            k,
            permutations,
            constrained: false,
        }
    }

    /// Build from all possible permutations of the given rule
    pub fn from_rule(rule: &InternalRule<T>) -> Self {
        Self::new(rule.super_cells.clone(), rule.num_mines, rule.permute())
    }

    /// Back-construct an [`InternalRule`] from this `PermutationSet`
    ///
    /// Note that the set generated from `Self::from_rule(self.to_rule())` may
    /// not match this set, as it cannot account for permutations removed from
    /// this set due to conflicts
    pub fn to_rule(&self) -> Result<InternalRule<T>, InconsistencyError> {
        InternalRule::new_count_cells(self.k, self.super_cells.clone())
    }

    /// Remove a permutation from the set, for example because that permutation
    /// conflicts with another rule
    pub fn remove(&mut self, permu: &Permutation<T>) {
        self.constrained = true;
        self.permutations.remove(permu);
    }

    /// Is this `PermutationSet` empty?
    pub fn is_empty(&self) -> bool {
        self.permutations.is_empty()
    }

    /// Create a new `PermutationSet` which is constrained to only those
    /// [`Permutation`]s that are compatible with the given one
    pub fn get_compatible(&self, permu: &Permutation<T>) -> Self {
        Self::new(
            self.super_cells.clone(),
            self.k,
            self.permutations
                .iter()
                .filter(|p| p.is_compatible(permu))
                .cloned()
                .collect(),
        )
    }

    /// Create a new `PermutationSet` consisting of only the sub-setted
    /// permutations from this set
    pub fn subset(
        &self,
        sub_cells: FrozenSet<FrozenSet<T>>,
    ) -> Result<Self, InconsistencyError> {
        let permu_subset = self
            .permutations
            .iter()
            .map(|p| p.subset(sub_cells.iter().cloned()))
            .collect::<HashSet<_>>();
        let mut k_sub = permu_subset
            .iter()
            .map(Permutation::k)
            .collect::<HashSet<_>>();
        if !k_sub.len() == 1 {
            // Subset is not valid because permutations differ in the number of mines
            Err(InconsistencyError(
                "The permutations in the subset differ in the number of mines they \
                 contain",
            ))
        } else {
            Ok(Self::new(
                sub_cells,
                pop(&mut k_sub).expect("Checked to exist"),
                permu_subset,
            ))
        }
    }

    /// See `force_decompose()`; optimises if set has not been constrained,
    /// because full permu-sets decompose to themselves
    pub fn decompose(self) -> HashSet<Self> {
        if self.constrained {
            self.force_decompose(1)
        } else {
            [self].into()
        }
    }

    /// Determine if this `PermutationSet` is the cartesian product of N smaller
    /// permutation sets; return the decomposition if so
    ///
    /// This set may be constrained, in which case at least one subset of the
    /// decomposition (if one exists) will also be constrained
    pub fn force_decompose(self, k_floor: usize) -> HashSet<Self> {
        for k in k_floor..=(self.super_cells.len() / 2) {
            for cell_subset in self
                .super_cells
                .iter()
                .cloned()
                .combinations(k)
                .map(|comb| comb.into_iter().collect::<FrozenSet<_>>())
            {
                if let Some((permu_subset, permu_remainder)) = self.split(&cell_subset)
                {
                    // We've found a cartesian divisor!
                    let mut divisors: HashSet<_> = [permu_subset].into();
                    divisors.extend(permu_remainder.force_decompose(k));
                    return divisors;
                }
            }
        }
        // No cartesian divisor found; this set is prime
        [self].into()
    }

    /// Helper function for `force_decompose()`. Given a subset of cells, return
    /// the two `PermutationSet`s for the subset and the set of the remaining
    /// cells, provided `cell_subset` is a valid decomposor.
    pub fn split(&self, cell_subset: &FrozenSet<FrozenSet<T>>) -> Option<(Self, Self)> {
        let cell_remainder = self
            .super_cells
            .difference(cell_subset)
            .cloned()
            .collect::<FrozenSet<_>>();
        let permu_subset = self.subset(cell_subset.clone()).ok()?;
        // Early returned if the subset cannot be a cartesian divisor (i.e. the set of
        // permutations could not have originated from a single 'choose' operation)

        // Get the remaining `PermutationSet`s for each sub-permutation
        let mut permu_remainders = map_reduce(
            self.permutations.iter().cloned(),
            |p| [(p.subset(cell_subset.iter().cloned()), p)].into_iter(),
            |pv| {
                pv.into_iter()
                    .map(|p| p.subset(cell_remainder.iter().cloned()))
                    .collect::<FrozenSet<_>>()
            },
        )
        .into_values()
        .collect::<HashSet<_>>();
        if permu_remainders.len() > 1 {
            // Remaining subsets are not identical for each sub-permutation; not a
            // cartesian divisor
            None
        } else {
            let permu_remainders = pop(&mut permu_remainders)?;
            let k = permu_subset.k;
            Some((
                permu_subset,
                PermutationSet::new(
                    cell_remainder,
                    self.k - k,
                    permu_remainders.thaw(),
                ),
            ))
        }
    }
}
impl<T: Cell> PartialEq for PermutationSet<T> {
    fn eq(&self, other: &Self) -> bool {
        self.super_cells == other.super_cells
            && self.k == other.k
            && self.permutations == other.permutations
    }
}
impl<T: Cell> Eq for PermutationSet<T> {
}
impl<T: Cell> Hash for PermutationSet<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.super_cells.hash(state);
        self.k.hash(state);
        self.permutations.clone().freeze().hash(state);
    }
}

/// A single permutation of N mines among a set of (super-)cells
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Permutation<T: Cell> {
    /// Super-cell -> Number of mines therein
    ///
    /// Cell set is determined implicitly from this mapping, so all cells in the
    /// set must have an entry - even if they have no mines
    mapping: HashMap<FrozenSet<T>, usize>,
}
impl<T: Cell> Hash for Permutation<T> {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.mapping.clone().freeze().hash(state);
    }
}
impl<T: Cell> Permutation<T> {
    pub fn new(mapping: HashMap<FrozenSet<T>, usize>) -> Self {
        Self {
            mapping,
        }
    }

    /// Return a sub-permutation containing only the cells in `sub_cells`
    pub fn subset(&self, sub_cells: impl Iterator<Item = FrozenSet<T>>) -> Self {
        Self::new(
            sub_cells
                .map(|cell| {
                    let val = self.mapping[&cell];
                    (cell, val)
                })
                .collect(),
        )
    }

    /// Is this permutation consistent with `other`? That is, do the cells they
    /// have in common have matching numbers of mines assigned.
    pub fn is_compatible(&self, other: &Self) -> bool {
        self.subset(self.cells().intersection(&other.cells()).cloned())
            == other.subset(self.cells().intersection(&other.cells()).cloned())
    }

    /// Return a new permutation by combining this permutation with `other`. The
    /// permutations must be compatible!
    pub fn combine(&self, other: &Self) -> Self {
        assert!(self
            .mapping
            .iter()
            .all(|(k, v)| !other.mapping.contains_key(k) || other.mapping[k] == *v));
        let mut mapping = self.mapping.clone();
        for (cell, num_mines) in &other.mapping {
            mapping.insert(cell.clone(), *num_mines);
        }
        Self::new(mapping)
    }

    /// Return the total number of mines in this permutation
    pub fn k(&self) -> usize {
        self.mapping.values().sum()
    }

    /// Return the set of cells in this permutation
    pub fn cells(&self) -> HashSet<FrozenSet<T>> {
        self.mapping.keys().cloned().collect()
    }

    /// Count the number of permutations this permutation would correspond to if
    /// each super-cell were broken up into singleton cells.
    ///
    /// E.G. N mines in a super-cell of M cells has (MCN) actual configurations.
    pub fn multiplicity(&self) -> usize {
        self.mapping
            .iter()
            .map(|(super_cell, &k)| choose(super_cell.len(), k))
            .product()
    }
}
