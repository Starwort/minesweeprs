#![feature(generators, generator_trait)]
//! # Minesweeprs
//!
//! This project is a port of [a minesweeper solver algorithm by @mrgriscom](https://github.com/mrgriscom/minesweepr). It is written in Rust and aims to improve performance compared to the original, and allow it to run in-browser via WebAssembly.
//!
//! ## Solving
//!
//! To solve a board, you provide a number of abstract 'rules' describing the game state, along with information about the board as a whole: total number of cells and total number of mines. The original project's 'cell mine probability' feature is also implemented, but does not have the same level of support.
//!
//! Each rule represents information gleaned from the uncovered cells of the board. A single `Rule` consists of a set of cells, along with how many mines are to be found among that set. So for a given uncovered cell (say we uncovered a 3), we'd generate: `Rule::new(3, [set of cells adjacent to the uncovered cell])`.
//!
//! *The solver does **not** have any concept of a grid, or the board's geometry. It just knows about specific sets of cells.*
//!
//! Here's an example (ASCII art taken from the original README):
//!
//! ```text
//! ..1Axxxxxx
//! ..2Bxxxxxx
//! ..3Cxxxxxx
//! ..2Dxxxxxx
//! 112Exxxxxx
//! IHGFxxxxxx
//! xxxxxxxxxx
//! xxxxxxxxxx
//! xxxxxxxxxx
//! xxxxxxxxxx
//! ```
//!
//! This is an easy-mode board; 10x10, with 10 mines. We've assigned a unique tag (`A`, `B`, `C`, ...) to each covered cell next to the uncovered region (henceforth referred to as a 'front' of play).
//!
//! This board can be solved with the following code:
//!
//! ```rust
//! use std::rc::Rc;
//! use minesweeprs::{solve, BoardInfo, Rule};
//! let output = solve(
//!     &[
//!         Rule::new(1, ["A", "B"]),
//!         Rule::new(2, ["A", "B", "C"]),
//!         Rule::new(3, ["B", "C", "D"]),
//!         Rule::new(2, ["C", "D", "E"]),
//!         Rule::new(2, ["D", "E", "F", "G", "H"]),
//!         Rule::new(1, ["G", "H", "I"]),
//!         Rule::new(1, ["H", "I"]),
//!     ],
//!     BoardInfo { total_cells: 85, total_mines: 10 },
//!     ".",
//! );
//! // The board is solvable, so the below should hold:
//! assert_eq!(
//!     output,
//!     Ok(
//!         [
//!             ("A", 0.0),
//!             ("B", 1.0),
//!             ("C", 1.0),
//!             ("D", 1.0),
//!             ("E", 0.0),
//!             ("F", 0.07792207792207793),
//!             ("G", 0.0),
//!             ("H", 0.9220779220779222),
//!             ("I", 0.07792207792207793),
//!             (".", 0.07792207792207792),
//!         ].into(),
//!     )
//! );
//! ```
//!
//! which will return a `Result<HashMap<char, f64>, InconsistencyError>` - a map of tags to probabilities. The `Result` will be `Ok` if the board is solvable, and `Err` if it is not (e.g. if the state is inconsistent/cowhich will return a `Result<HashMap<char, f64>, InconsistencyError>` - a map of tags to probabilities. The `Result` will be `Ok` if the board is solvable, and `Err` if it is not (e.g. if the state is inconsistent/contradictory, or there is no possible solution).ntradictory, or there is no possible solution).
//!
//! (although the keys will be in a random order)
//!
//! From this we see that `B`, `C`, and `D` are guaranteed to be mines, `A`, `E`, and `G` are guaranteed to be safe, `H` is 92.21% likely to be a mine, and `F`, `I`, and all other cells (represented by the tag `.`) are all 7.79% likely to be mines.
//!
//! Note that `total_cells` was passed as 85 instead of 100. This is because 15 cells are uncovered, and were not included in any rule. The solver does not know anything about the geometry of the grid, so these cells are simply subtracted from the total number of cells and the solver never even needs to know they exist. Alternatively, there could be a rule `Rule::new(0, [set of all uncovered cells])` and set `total_cells` to 100. Technically, we could make a separate `Rule` for every single uncovered cell, but that is cumbersome and inefficient.
//!
//! In general, `total_cells` must equal the number of all covered cells in the grid, plus the number of uncovered cells that happen to be included in a rule. `total_mines` must equal the total number of mines in the grid, minus any mines that have been identified and *not* mentioned in any `Rule` (or the solver will try to place them in uncovered cells!).
//!
//! You can see that the specific logic for generating the appropriate arguments to `solve()` is quite nuanced (assuming you don't take the naive route). Luckily, utility code is provided that can do the processing for you. See `minesweepr::util::Board::generate_rules()`. You can also use `minesweepr::util::read_board()` (without the explicit tagging `A`, `B`, `C` that was done above for illustrative purposes).
//!
//! ## Interactive demo (FUTURE FEATURE)
//!
//! An interactive player is [will be] provided in `web_demo/` as a simple web app. All game logic and rendering is client-side JavaScript; board solving is done via WebAssembly and a web worker (to avoid freezing the UI thread).
//!
//! ## Future work
//!
//! In the future, I'd like to find a way to optimise out as many of the `Rc`s (and `RefCell`/`Shared`s) as possible, ideally ending with zero-clone data structures. This would improve performance, possibly significantly. I'm not sure if this is possible, but perhaps someone with more experience optimising allocations could help with this.
//!
//! Additionally, I would like to reduce or remove the reliance on the nightly compiler. This is currently required for the features `generators` and `generator_trait`. These features are used to create Python-style generator iterators. Removing these generators without introducing boxed iterators would probably require a significant amount of boilerplate, so I'm not sure if it's worth it.
use std::collections::{HashMap, HashSet};

use either::Either;
use frozenset::FrozenSet;
use itertools::Itertools;
use solve::{
    FixedProbTally,
    FrontTally,
    InconsistencyError,
    InternalRule,
    PermutedRuleset,
    RuleReducer,
    UnchartedCell,
};
use internal_util::{fact_div, map_reduce};

mod solve;
mod internal_util;
pub mod util;

pub use solve::{MinePrevalence, Rule, Cell, MineCount};

/// Solve a minesweeper board.
///
/// Take in a minesweeper board and return the solution as a mapping of each
/// cell to its probability of being a mine.
///
/// # Arguments
///
/// - `rules`: A list of [`Rule`]s describing the board.
/// - `mine_prevalence`: Either information about the board, or the probability
///   of any unknown cell being a mine (if the total number of mines is not
///   known).
/// - `other_tag`: A value used to represent all 'other' cells (all cells not
///   mentioned in a rule) in the solution output.
///
/// # Errors
///
/// Returns an [`InconsistencyError`] if the rules are logically inconsistent -
/// for example, if the total number of mines is known, but the rules imply a
/// different number of mines or if there are more mines than cells (either
/// globally, or within a rule).
pub fn solve<T: Cell>(
    rules: &[Rule<T>],
    mine_prevalence: impl Into<MinePrevalence>,
    other_tag: &T,
) -> Result<HashMap<T, f64>, InconsistencyError> {
    let mine_prevalence = mine_prevalence.into().0;
    let (internal_rules, all_cells) = condense_super_cells(rules)?;
    let mut reduced = reduce_rules(internal_rules.into_iter())?;
    let mut determined = reduced
        .iter()
        .filter(|rule| rule.is_trivial())
        .cloned()
        .collect::<HashSet<_>>();
    reduced.retain(|rule| !rule.is_trivial());

    let ruleset = permute_and_interfere(reduced)?;
    let mut fronts = ruleset.split_fronts();

    determined.extend(
        fronts
            .iter()
            .filter(|front| front.is_trivial())
            .map(PermutedRuleset::trivial_rule),
    );
    fronts.retain(|front| !front.is_trivial());

    let mut stats = fronts
        .iter()
        .map(enumerate_front)
        .collect::<Result<Vec<_>, _>>()?;
    stats.extend(determined.iter().map(InternalRule::tally));
    let cell_probs = cell_probabilities(stats, mine_prevalence, &all_cells)?;
    Ok(expand_cells(cell_probs, other_tag))
}

/// Condense cells into super-cells by finding sets of ordinary cells that only
/// ever appear together.
///
/// Returns a set of [`InternalRule`] corresponding to the original ruleset.
///
/// Note that *all* cells are converted to super-cells for ease of processing
/// later, even if that cell does not group with any others. The result would be
/// a singleton super-cell.
#[allow(clippy::type_complexity)]
fn condense_super_cells<T: Cell>(
    rules: &[Rule<T>],
) -> Result<(Vec<InternalRule<T>>, Vec<FrozenSet<T>>), InconsistencyError> {
    let cell_rules_map = map_reduce(
        rules.iter(),
        |rule| rule.cells.iter().map(|cell| (cell.clone(), rule.clone())),
        |vals| vals.into_iter().collect::<FrozenSet<_>>(),
    );
    let rules_super_cell_map = map_reduce(
        cell_rules_map.iter(),
        |(cell, rule)| [(rule.clone(), cell.clone())].into_iter(),
        |vals| vals.into_iter().collect::<FrozenSet<_>>(),
    );
    let rule_super_cells_map = map_reduce(
        rules_super_cell_map.iter(),
        |(rules, cell)| rules.iter().map(|rule| (rule.clone(), cell.clone())),
        |vals| vals.into_iter().collect::<FrozenSet<_>>(),
    );
    Ok((
        rules
            .iter()
            .map(|rule| rule.condensed(&rule_super_cells_map))
            .collect::<Result<_, _>>()?,
        rules_super_cell_map.values().cloned().collect(),
    ))
}

/// Reduce the ruleset using logical deduction
fn reduce_rules<T: Cell>(
    rules: impl Iterator<Item = InternalRule<T>>,
) -> Result<HashSet<InternalRule<T>>, InconsistencyError> {
    let mut reducer = RuleReducer::new();
    reducer.add_rules(rules)?;
    reducer.reduce_all()
}

/// Process the set of rules and analyse the relationships and constraints among
/// them
fn permute_and_interfere<T: Cell>(
    rules: HashSet<InternalRule<T>>,
) -> Result<PermutedRuleset<T>, InconsistencyError> {
    let mut ruleset = PermutedRuleset::new(rules);
    ruleset.cross_eliminate()?;
    ruleset.rereduce()?;
    Ok(ruleset)
}

/// Enumerate and tabulate all mine configurations for the given front
///
/// Return a tally where: Sub-totals are split out by total number of mines in
/// the configuration, and each sub-tally contains a total count of matching
/// configurations as well as an expected number of mines in each cell
fn enumerate_front<T: Cell>(
    ruleset: &PermutedRuleset<T>,
) -> Result<FrontTally<T>, InconsistencyError> {
    let mut tally = FrontTally::new();
    tally.tally(ruleset)?;
    Ok(tally)
}

/// Generate the final expected values for all cells in all fronts
///
/// - `tallies`: A set of [`FrontTally`]s, one for each front
/// - `mine_prevalence`: Either information about the board, or the probability
///   of any unknown cell being a mine (if the total number of mines is not
///   known).
/// - `all_cells`: A set of all super-cells from all rules
fn cell_probabilities<T: Cell>(
    mut tallies: Vec<FrontTally<T>>,
    mine_prevalence: Either<MineCount, f64>,
    all_cells: &[FrozenSet<T>],
) -> Result<HashMap<Either<FrozenSet<T>, UnchartedCell>, f64>, InconsistencyError> {
    let tally_uncharted = match mine_prevalence {
        Either::Left(mine_prevalence) => {
            let num_uncharted_cells =
                check_count_consistency(&tallies, mine_prevalence, all_cells)?;

            let num_static_mines = tallies
                .iter()
                .filter_map(|tally| {
                    if tally.is_static() {
                        Some(tally.max_mines())
                    } else {
                        None
                    }
                })
                .sum::<usize>();
            let at_large_mines = mine_prevalence.total_mines - num_static_mines;

            Either::Left(combine_fronts(
                tallies
                    .iter_mut()
                    .filter(|tally| !tally.is_static())
                    .collect_vec(),
                num_uncharted_cells,
                at_large_mines,
            )?)
        },
        Either::Right(mine_prevalence) => {
            Either::Right(weight_nondiscrete(
                tallies.iter_mut().filter(|tally| !tally.is_static()),
                mine_prevalence,
            )?)
        },
    };
    Ok(tallies
        .into_iter()
        .flat_map(|tally| tally.collapse().into_iter())
        .chain(match tally_uncharted {
            Either::Left(tally) => tally.collapse().into_iter(),
            Either::Right(tally) => tally.collapse().into_iter(),
        })
        .collect())
}

/// Back-convert the expected values for all super-cells into per-cell
/// probabilities for each individual cell
#[allow(clippy::cast_precision_loss)]
fn expand_cells<T: Cell>(
    cell_probs: HashMap<Either<FrozenSet<T>, UnchartedCell>, f64>,
    other_tag: &T,
) -> HashMap<T, f64> {
    cell_probs
        .into_iter()
        .flat_map(|(super_cell, p)| {
            match super_cell {
                Either::Left(super_cell) => {
                    let len = super_cell.len() as f64;
                    super_cell
                        .into_iter()
                        .map(|cell| (cell, p / len))
                        .collect_vec()
                        .into_iter()
                },
                Either::Right(uncharted) => {
                    uncharted
                        .iter()
                        .next()
                        .map(|_| (other_tag.clone(), p / uncharted.len() as f64))
                        .into_iter()
                        .collect_vec()
                        .into_iter()
                },
            }
        })
        .collect()
}

/// Ensure the min/max mines required across all fronts is compatible with the
/// total number of mines and remaining space available on the board
///
/// In the process, computer and return the remaining available space (number of
/// 'other' cells not referenced in any rule)
fn check_count_consistency<T: Cell>(
    tallies: &[FrontTally<T>],
    mine_prevalence: MineCount,
    all_cells: &[FrozenSet<T>],
) -> Result<usize, InconsistencyError> {
    let (min_possible_mines, max_possible_mines) = possible_mine_limits(tallies.iter());
    let num_uncharted_cells = mine_prevalence.total_cells
        - all_cells
            .iter()
            .map(|super_cell| super_cell.len())
            .sum::<usize>();

    if min_possible_mines > mine_prevalence.total_mines {
        Err(InconsistencyError(
            "Minimum possible number of mines is more than supplied mine count",
        ))
    } else if mine_prevalence.total_mines > max_possible_mines + num_uncharted_cells {
        Err(InconsistencyError(
            "Maximum possible number of mines is less than supplied mine count",
        ))
    } else {
        Ok(num_uncharted_cells)
    }
}

/// Assign relative weights to all sub-tallies in all fronts. Because the total
/// number of mines is fixed, we must do a combinatorial analysis to compute the
/// likelihood of each front containing each possible number of mines. In the
/// process, compute the mine count likelihood for the 'other' cells, not a part
/// of any front, and return a meta-front encapsulating them.
fn combine_fronts<T: Cell>(
    tallies: Vec<&mut FrontTally<T>>,
    num_uncharted_cells: usize,
    at_large_mines: usize,
) -> Result<FrontTally<T>, InconsistencyError> {
    use solve::combine::CombinedFront;
    let (min_tallied_mines, max_tallied_mines) =
        possible_mine_limits(tallies.iter().map(|tally| &**tally));
    let min_other_mines = at_large_mines - max_tallied_mines.min(at_large_mines);
    // `min_tallied_mines` is known to be <= `at_large_mines` due to
    // `check_count_consistency()`
    let max_other_mines = (at_large_mines - min_tallied_mines).min(num_uncharted_cells);

    let relative_likelihood = |num_free_mines: usize| {
        discrete_relative_likelihood(
            num_uncharted_cells,
            num_free_mines,
            max_other_mines,
        )
    };

    let all_fronts = tallies
        .iter()
        .map(|tally| CombinedFront::from_tally(tally))
        .chain(
            [CombinedFront::for_other(
                min_other_mines,
                max_other_mines,
                relative_likelihood,
            )?]
            .into_iter(),
        )
        .collect_vec();
    let (mut min_remaining_mines, mut max_remaining_mines) = all_fronts
        .iter()
        .map(solve::combine::CombinedFront::min_max_mines)
        .reduce(|(total_min, total_max), (min, max)| (total_min + min, total_max + max))
        .expect("all_fronts always has at least one element");
    let mut combined = CombinedFront::null();
    for front in all_fronts {
        // Note that it's only safe to use min/max mines in this way before the front
        // has been combined/modified
        let (front_min, front_max) = front.min_max_mines();
        min_remaining_mines -= front_min;
        max_remaining_mines -= front_max;
        combined = combined.join_with(
            &front,
            min_remaining_mines,
            max_remaining_mines,
            at_large_mines,
        );
    }
    let (uncharted_total, front_totals) = {
        let mut front_totals = combined.collapse().collect_vec();
        (
            front_totals
                .pop()
                .expect("front_totals always has at least one element"),
            front_totals,
        )
    };
    for (tally, front_total) in tallies.into_iter().zip(front_totals) {
        tally.update_weights(&front_total);
    }

    Ok(FrontTally::for_other(num_uncharted_cells, &uncharted_total))
}

/// Get the total minimum and maximum possible number of mines across all
/// tallied fronts
fn possible_mine_limits<'a, T: Cell + 'a>(
    tallies: impl Iterator<Item = &'a FrontTally<T>>,
) -> (usize, usize) {
    tallies.fold((0, 0), |(min_mines, max_mines), tally| {
        (min_mines + tally.min_mines(), max_mines + tally.max_mines())
    })
}

/// '`num_uncharted_cells` choose `num_free_mines`' / '`num_uncharted_cells`
/// choose `max_other_mines`'
fn discrete_relative_likelihood(
    num_uncharted_cells: usize,
    num_free_mines: usize,
    max_other_mines: usize,
) -> Result<f64, InconsistencyError> {
    if num_free_mines > num_uncharted_cells || max_other_mines > num_uncharted_cells {
        Err(InconsistencyError(
            "num_free_mines, max_other_mines must be [0, num_uncharted_cells]",
        ))
    } else {
        Ok(fact_div(max_other_mines, num_free_mines)
            * fact_div(
                num_uncharted_cells - max_other_mines,
                num_uncharted_cells - num_free_mines,
            ))
    }
}

/// Weight the relative likelihood of each sub-tally in a 'fixed mine
/// probability/variable number of mines'-style game
///
/// In this scenario, all fronts are completely independent; no front affects
/// the likelihoods for any other front
fn weight_nondiscrete<'a, T: Cell + 'a>(
    dyn_tallies: impl Iterator<Item = &'a mut FrontTally<T>>,
    mine_prevalence: f64,
) -> Result<FixedProbTally, InconsistencyError> {
    for tally in dyn_tallies {
        let min_mines = tally.min_mines();
        tally.scale_weights(|num_mines| {
            nondiscrete_relative_likelihood(mine_prevalence, num_mines, min_mines)
        })?;
    }

    // Regurgitate the fixed mine probability as the p for 'other' cells. Kinda
    // redundant, but saves the client a step. Note that since we don't count the
    // total number of cells in this mode, this is *not* a guarantee that any given
    // game state actually *has* other cells
    Ok(FixedProbTally(mine_prevalence))
}

/// Given the binomial probability (p, k, n => p^k * (1-p)^(n-k)), calculate
/// `binom_prob(mine_prevalence, num_mines, n) / binom_prob(mine_prevalence,
/// min_mines, n)`
///
/// Note that n isn't actually needed! This is because we're calculating a
/// per-configuration weight, and in a true binomial distribution we'd then
/// multiply by nCk configurations; however, that has effectively been done by
/// the enumeration/tallying phase
fn nondiscrete_relative_likelihood(
    mine_prevalence: f64,
    num_mines: usize,
    min_mines: usize,
) -> Result<f64, InconsistencyError> {
    let p = mine_prevalence;
    #[allow(clippy::cast_precision_loss)]
    let k = num_mines as f64;
    #[allow(clippy::cast_precision_loss)]
    let k0 = min_mines as f64;
    if (0.0..=1.0).contains(&p) {
        Ok((p / (1.0 - p)).powf(k - k0))
    } else {
        Err(InconsistencyError("p must be [0, 1]"))
    }
}

#[cfg(test)]
mod full {
    use pretty_assertions::assert_eq;

    use super::*;

    #[test]
    fn readme_example() {
        let output = solve(
            &[
                Rule::new(1, ['A', 'B']),
                Rule::new(2, ['A', 'B', 'C']),
                Rule::new(3, ['B', 'C', 'D']),
                Rule::new(2, ['C', 'D', 'E']),
                Rule::new(2, ['D', 'E', 'F', 'G', 'H']),
                Rule::new(1, ['G', 'H', 'I']),
                Rule::new(1, ['H', 'I']),
            ],
            MineCount {
                total_cells: 85,
                total_mines: 10,
            },
            &'.',
        )
        .map(|output| {
            let mut output = output.into_iter().collect::<Vec<_>>();
            output.sort_by_key(|(c, _)| *c);
            output
        });
        assert_eq!(
            output,
            Ok(vec![
                ('.', 0.077_922_077_922_077_92),
                ('A', 0.0),
                ('B', 1.0),
                ('C', 1.0),
                ('D', 1.0),
                ('E', 0.0),
                ('F', 0.077_922_077_922_077_93),
                ('G', 0.0),
                ('H', 0.922_077_922_077_922_2),
                ('I', 0.077_922_077_922_077_93),
            ]),
        );
    }
}

#[cfg(test)]
#[allow(clippy::too_many_lines)] // tests are long
mod unit {
    use frozenset::Freeze;
    use pretty_assertions::assert_eq;

    use super::solve::{Permutation, PermutationSet, Reduceable};
    use super::*;
    fn r(num_mines: usize, cells: &'static str) -> Rule<char> {
        Rule::new(num_mines, cells.chars())
    }
    fn maybe_ir(
        num_mines: usize,
        cells: &'static str,
    ) -> Result<InternalRule<char>, InconsistencyError> {
        let super_cells = cells
            .split(',')
            .filter(|str| !str.is_empty())
            .map(str::chars);
        InternalRule::from_data(num_mines, super_cells)
    }
    fn ir(num_mines: usize, cells: &'static str) -> InternalRule<char> {
        maybe_ir(num_mines, cells).unwrap_or_else(|_| panic!("{num_mines}:{cells}"))
    }

    fn p<const N: usize>(spec: [(usize, &'static str); N]) -> Permutation<char> {
        Permutation::new(
            spec.into_iter()
                .map(|(k, cells)| (cells.chars().collect(), k))
                .collect(),
        )
    }

    #[allow(clippy::needless_pass_by_value)]
    fn pset(rule: InternalRule<char>) -> HashSet<Permutation<char>> {
        PermutationSet::from_rule(&rule).permutations
    }

    #[test]
    fn test_rule_init() {
        assert_eq!(ir(0, "").num_cells, 0);
        assert_eq!(ir(0, "a").num_cells, 1);
        assert_eq!(ir(0, "a,b,c").num_cells, 3);
        assert_eq!(ir(0, "ab,c").num_cells, 3);
        assert_eq!(ir(0, "abc").num_cells, 3);
        assert_eq!(ir(0, "abc,de").num_cells, 5);

        maybe_ir(1, "").expect_err("1: is a non-sensical rule (too many mines)");
        maybe_ir(2, "a").expect_err("2:a is a non-sensical rule (too many mines)");
        maybe_ir(4, "ab,c")
            .expect_err("4:ab,c is a non-sensical rule (too many mines)");

        assert_eq!(ir(1, "a").num_mines, 1);
        assert_eq!(ir(3, "ab,c").num_mines, 3);
    }

    #[test]
    fn test_rule_decompose() {
        assert_eq!(ir(0, "").decompose(), vec![]);
        assert_eq!(ir(0, "a").decompose(), vec![ir(0, "a")],);
        assert_eq!(ir(1, "a").decompose(), vec![ir(1, "a")],);
        assert_eq!(
            ir(0, "abc,de,f")
                .decompose()
                .into_iter()
                .collect::<HashSet<_>>(),
            [ir(0, "abc"), ir(0, "de"), ir(0, "f"),].into(),
        );
        assert_eq!(ir(1, "abc,de,f").decompose(), vec![ir(1, "abc,de,f")],);
        assert_eq!(ir(5, "abc,de,f").decompose(), vec![ir(5, "abc,de,f")],);
        assert_eq!(
            ir(6, "abc,de,f")
                .decompose()
                .into_iter()
                .collect::<HashSet<_>>(),
            [ir(3, "abc"), ir(2, "de"), ir(1, "f")].into(),
        );
    }

    #[test]
    fn test_rule_subtract() {
        assert!(ir(0, "").is_subrule_of(&ir(0, "")));
        assert!(ir(0, "").is_subrule_of(&ir(2, "ab,c")));
        assert!(ir(2, "ab,c").is_subrule_of(&ir(2, "ab,c")));
        assert!(ir(0, "c").is_subrule_of(&ir(2, "ab,c")));
        assert!(ir(1, "ab").is_subrule_of(&ir(2, "ab,c")));
        assert!(ir(1, "ab").is_subrule_of(&ir(1, "ab,c")));
        assert!(!ir(1, "a,b").is_subrule_of(&ir(1, "a,c")));

        // These should not occur in practice
        assert!(!ir(1, "a,b").is_subrule_of(&ir(1, "ab")));
        assert!(!ir(1, "ab").is_subrule_of(&ir(1, "a,b")));
        assert!(!ir(1, "ab").is_subrule_of(&ir(1, "a")));
        assert!(!ir(1, "a").is_subrule_of(&ir(1, "ab")));

        assert_eq!(ir(0, "").subtract(&ir(0, "")).expect("0: - 0:"), ir(0, ""),);
        assert_eq!(
            ir(2, "ab,c").subtract(&ir(0, "")).expect("2:ab,c - 0:"),
            ir(2, "ab,c"),
        );
        assert_eq!(
            ir(2, "ab,c")
                .subtract(&ir(2, "ab,c"))
                .expect("2:ab,c - 2:ab,c"),
            ir(0, ""),
        );
        ir(2, "ab,c").subtract(&ir(1, "ab,c")).expect_err(
            "2:ab,c - 1:ab,c is non-sensical (1:ab,c is not a subrule of 2:ab,c - \
             mismatched mine counts)",
        );
        ir(1, "ab,c").subtract(&ir(2, "ab")).expect_err(
            "1:ab,c - 2:ab is non-sensical (2:ab is not a subrule of 1:ab,c - more \
             mines in a subset of the cells)",
        );
        assert_eq!(
            ir(2, "ab,c").subtract(&ir(0, "c")).expect("2:ab,c - 0:c"),
            ir(2, "ab"),
        );
        assert_eq!(
            ir(2, "ab,c").subtract(&ir(1, "ab")).expect("2:ab,c - 1:ab"),
            ir(1, "c"),
        );
        assert_eq!(
            ir(1, "ab,c").subtract(&ir(1, "ab")).expect("1:ab,c - 1:ab"),
            ir(0, "c"),
        );
    }

    #[test]
    fn test_rule_trivial() {
        assert!(ir(1, "a").is_trivial());
        assert!(ir(1, "ab").is_trivial());
        assert!(!ir(1, "a,b").is_trivial());
    }

    #[test]
    fn test_condense_super_cells() {
        #[allow(clippy::needless_pass_by_value)]
        fn compare<const N: usize>(
            raw_rules: [Rule<char>; N],
            out_rules: [InternalRule<char>; N],
            super_cells: &'static str,
        ) {
            let (rules, cells) =
                condense_super_cells(&raw_rules).unwrap_or_else(|err| {
                    panic!(
                        "condense_super_cells({raw_rules:?}, {out_rules:?}, \
                         {super_cells:?}) failed: {err:?}"
                    )
                });
            assert_eq!(rules, &out_rules);
            assert_eq!(cells.len(), cells.iter().collect::<HashSet<_>>().len());
            assert_eq!(
                cells.iter().cloned().collect::<FrozenSet<_>>(),
                ir(0, super_cells).super_cells,
            );
        }
        compare([r(0, "")], [ir(0, "")], "");
        compare([r(1, "a")], [ir(1, "a")], "a");
        compare([r(1, "a"), r(1, "a")], [ir(1, "a"), ir(1, "a")], "a");
        compare([r(1, "ab")], [ir(1, "ab")], "ab");
        compare(
            [r(1, "ab"), r(2, "cd")],
            [ir(1, "ab"), ir(2, "cd")],
            "ab,cd",
        );
        compare([r(1, "ab"), r(1, "b")], [ir(1, "a,b"), ir(1, "b")], "a,b");
        compare(
            [r(1, "ab"), r(2, "bc")],
            [ir(1, "a,b"), ir(2, "b,c")],
            "a,b,c",
        );
        compare(
            [r(1, "abc"), r(2, "bcd")],
            [ir(1, "a,bc"), ir(2, "bc,d")],
            "a,bc,d",
        );
        compare(
            [r(1, "abc"), r(2, "bcd"), r(0, "ce")],
            [ir(1, "a,b,c"), ir(2, "b,c,d"), ir(0, "c,e")],
            "a,b,c,d,e",
        );
        compare(
            [r(1, "abc"), r(2, "bcd"), r(0, "bcef")],
            [ir(1, "a,bc"), ir(2, "bc,d"), ir(0, "bc,ef")],
            "a,bc,d,ef",
        );
    }

    #[test]
    fn test_rule_reduce_metric() {
        // Super-cells don't matter
        assert_eq!(
            Reduceable::new(ir(3, "a,b,cde"), ir(1, "a,b"),)
                .expect("3:a,b,cde > 1:a,b")
                .metric(),
            Reduceable::new(ir(3, "a,b,c,d,e"), ir(1, "ab"),)
                .expect("3:a,b,c,d,e > 1:ab")
                .metric(),
        );
        // Prefer bigger super-rule
        assert!(
            Reduceable::new(ir(3, "a,b,c,d,e"), ir(1, "a,b"),)
                .expect("3:a,b,c,d,e > 1:a,b")
                > Reduceable::new(ir(3, "a,b,c,d"), ir(2, "b,c,d"),)
                    .expect("3:a,b,c,d > 2:b,c,d"),
        );
        // ...then prefer bigger sub-rule
        assert!(
            Reduceable::new(ir(3, "a,b,c,d"), ir(2, "b,c,d"),)
                .expect("3:a,b,c,d > 2:b,c,d")
                > Reduceable::new(ir(3, "a,b,c,d"), ir(2, "b,c"),)
                    .expect("3:a,b,c > 2:b,c"),
        );
        // ...then prefer smallest # permutations post-reduction
        assert!(
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(1, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 1:a,b,c,d")
                > Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(2, "a,b,c,d"))
                    .expect("4:a,b,c,d,e,f,g,h > 2:a,b,c,d")
        );
        assert!(
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(0, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 0:a,b,c,d")
                > Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(1, "a,b,c,d"))
                    .expect("4:a,b,c,d,e,f,g,h > 1:a,b,c,d")
        );
        assert_eq!(
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(1, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 1:a,b,c,d")
                .metric(),
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(3, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 3:a,b,c,d")
                .metric(),
        );
        assert_eq!(
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(0, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 0:a,b,c,d")
                .metric(),
            Reduceable::new(ir(4, "a,b,c,d,e,f,g,h"), ir(4, "a,b,c,d"))
                .expect("4:a,b,c,d,e,f,g,h > 4:a,b,c,d")
                .metric(),
        );
    }

    #[test]
    fn test_reduce_rules() {
        // Degenerate rules disappear
        assert_eq!(reduce_rules([ir(0, "")].into_iter()), Ok([].into()));
        assert_eq!(
            reduce_rules([ir(1, "a")].into_iter()),
            Ok([ir(1, "a")].into())
        );

        // Duplicate rules disappear
        assert_eq!(
            reduce_rules([ir(1, "a"), ir(1, "a")].into_iter()),
            Ok([ir(1, "a")].into())
        );
        assert_eq!(
            reduce_rules([ir(1, "a,b"), ir(1, "a,c")].into_iter()),
            Ok([ir(1, "a,b"), ir(1, "a,c")].into())
        );
        assert_eq!(
            reduce_rules([ir(2, "a,b,c,d,e,f,g"), ir(1, "f,g")].into_iter()),
            Ok([ir(1, "a,b,c,d,e"), ir(1, "f,g")].into())
        );
        assert_eq!(
            reduce_rules([ir(2, "a,b,x"), ir(1, "b"), ir(1, "b,c")].into_iter()),
            Ok([ir(1, "a,x"), ir(1, "b"), ir(0, "c")].into())
        );

        // Chained reduction
        assert_eq!(
            reduce_rules(
                [ir(2, "a,x,y,z"), ir(2, "a,b,x"), ir(1, "b"), ir(1, "b,c")]
                    .into_iter()
            ),
            Ok([ir(1, "a,x"), ir(1, "b"), ir(0, "c"), ir(1, "y,z")].into())
        );

        // Decomposition then reduction
        assert_eq!(
            reduce_rules([ir(1, "a,b,c,d"), ir(0, "c,d,e")].into_iter()),
            Ok([ir(1, "a,b"), ir(0, "c"), ir(0, "d"), ir(0, "e")].into())
        );
        assert_eq!(
            reduce_rules([ir(3, "a,b,c,d"), ir(3, "c,d,e")].into_iter()),
            Ok([ir(1, "a,b"), ir(1, "c"), ir(1, "d"), ir(1, "e")].into())
        );
    }

    #[test]
    fn test_permute() {
        assert_eq!(pset(ir(0, "")), [p([])].into());
        assert_eq!(pset(ir(0, "a")), [p([(0, "a")])].into());
        assert_eq!(pset(ir(1, "a")), [p([(1, "a")])].into());
        assert_eq!(pset(ir(0, "abc")), [p([(0, "abc")])].into());
        assert_eq!(pset(ir(1, "abc")), [p([(1, "abc")])].into());
        assert_eq!(pset(ir(2, "abc")), [p([(2, "abc")])].into());
        assert_eq!(pset(ir(3, "abc")), [p([(3, "abc")])].into());
        assert_eq!(
            pset(ir(0, "a,b,c")),
            [p([(0, "a"), (0, "b"), (0, "c")])].into()
        );
        assert_eq!(
            pset(ir(1, "a,b,c")),
            [
                p([(1, "a"), (0, "b"), (0, "c")]),
                p([(0, "a"), (1, "b"), (0, "c")]),
                p([(0, "a"), (0, "b"), (1, "c")]),
            ]
            .into(),
        );
        assert_eq!(
            pset(ir(2, "a,b,c")),
            [
                p([(1, "a"), (1, "b"), (0, "c")]),
                p([(1, "a"), (0, "b"), (1, "c")]),
                p([(0, "a"), (1, "b"), (1, "c")]),
            ]
            .into(),
        );
        assert_eq!(
            pset(ir(3, "a,b,c")),
            [p([(1, "a"), (1, "b"), (1, "c")])].into(),
        );
        assert_eq!(
            pset(ir(0, "abc,de,f")),
            [p([(0, "abc"), (0, "de"), (0, "f")])].into(),
        );
        assert_eq!(
            pset(ir(1, "abc,de,f")),
            [
                p([(1, "abc"), (0, "de"), (0, "f")]),
                p([(0, "abc"), (1, "de"), (0, "f")]),
                p([(0, "abc"), (0, "de"), (1, "f")]),
            ]
            .into(),
        );
        assert_eq!(
            pset(ir(3, "abc,de,f")),
            [
                p([(3, "abc"), (0, "de"), (0, "f")]),
                p([(2, "abc"), (1, "de"), (0, "f")]),
                p([(2, "abc"), (0, "de"), (1, "f")]),
                p([(1, "abc"), (2, "de"), (0, "f")]),
                p([(1, "abc"), (1, "de"), (1, "f")]),
                p([(0, "abc"), (2, "de"), (1, "f")]),
            ]
            .into(),
        );
        assert_eq!(
            pset(ir(5, "abc,de,f")),
            [
                p([(3, "abc"), (2, "de"), (0, "f")]),
                p([(3, "abc"), (1, "de"), (1, "f")]),
                p([(2, "abc"), (2, "de"), (1, "f")]),
            ]
            .into(),
        );
        assert_eq!(
            pset(ir(6, "abc,de,f")),
            [p([(3, "abc"), (2, "de"), (1, "f")])].into(),
        );
    }

    #[test]
    fn test_permuation_subset() {
        assert_eq!(
            p([(2, "abc"), (1, "de"), (0, "f")])
                .subset(ir(0, "abc,de").super_cells.into_iter()),
            p([(2, "abc"), (1, "de")]),
        );
        assert_eq!(
            p([(2, "abc"), (1, "de"), (0, "f")])
                .subset(ir(0, "f").super_cells.into_iter()),
            p([(0, "f")]),
        );
        assert_eq!(
            p([(2, "abc"), (1, "de"), (0, "f")])
                .subset(ir(0, "").super_cells.into_iter()),
            p([]),
        );
    }

    #[test]
    fn test_permutation_compatible_and_combine() {
        assert!(p([]).is_compatible(&p([])));
        assert!(p([(0, "a")]).is_compatible(&p([])));
        assert!(p([(0, "a")]).is_compatible(&p([(0, "a")])));
        assert!(p([(1, "a")]).is_compatible(&p([(1, "a")])));
        assert!(p([(0, "a")]).is_compatible(&p([(1, "b")])));
        assert!(!p([(0, "a")]).is_compatible(&p([(1, "a")])));
        assert!(p([(2, "abc"), (1, "de"), (0, "f")]).is_compatible(&p([
            (2, "abc"),
            (1, "de"),
            (2, "ghi")
        ])));
        assert!(!p([(1, "abc"), (1, "de"), (0, "f")]).is_compatible(&p([
            (2, "abc"),
            (1, "de"),
            (2, "ghi")
        ])));

        assert_eq!(p([]).combine(&p([])), p([]));
        assert_eq!(p([(0, "a")]).combine(&p([])), p([(0, "a")]));
        assert_eq!(p([(0, "a")]).combine(&p([(0, "a")])), p([(0, "a")]));
        assert_eq!(p([(1, "a")]).combine(&p([(1, "a")])), p([(1, "a")]));
        assert_eq!(
            p([(0, "a")]).combine(&p([(1, "b")])),
            p([(0, "a"), (1, "b")])
        );
        assert_eq!(
            p([(2, "abc"), (1, "de"), (0, "f")]).combine(&p([
                (2, "abc"),
                (1, "de"),
                (2, "ghi")
            ])),
            p([(2, "abc"), (1, "de"), (0, "f"), (2, "ghi")]),
        );
    }

    #[test]
    fn test_permutation_multiplicity() {
        assert_eq!(
            p([(0, "a"), (1, "b"), (0, "c"), (1, "d")]).multiplicity(),
            1
        );
        assert_eq!(
            p([(0, "ab"), (3, "def"), (0, "ghij"), (1, "k")]).multiplicity(),
            1
        );
        assert_eq!(
            p([(0, "ab"), (1, "def"), (0, "ghij"), (1, "k")]).multiplicity(),
            3
        );
        assert_eq!(
            p([(0, "ab"), (1, "def"), (2, "ghij"), (1, "k")]).multiplicity(),
            18
        );
    }

    #[test]
    fn test_permutationset_decompose() {
        let mut pset = PermutationSet::from_rule(&ir(2, "a,b,c,d"));
        assert_eq!(pset.clone().decompose(), [pset.clone()].into());
        pset.remove(&p([(1, "a"), (1, "b"), (0, "c"), (0, "d")]));
        assert_eq!(pset.clone().decompose(), [pset.clone()].into());
        pset.remove(&p([(0, "a"), (0, "b"), (1, "c"), (1, "d")]));
        assert_eq!(
            pset.clone().decompose(),
            [
                PermutationSet::from_rule(&ir(1, "a,b")),
                PermutationSet::from_rule(&ir(1, "c,d")),
            ]
            .into(),
        );
        pset.remove(&p([(1, "a"), (0, "b"), (0, "c"), (1, "d")]));
        assert_eq!(pset.clone().decompose(), [pset.clone()].into());
        pset.remove(&p([(0, "a"), (1, "b"), (0, "c"), (1, "d")]));
        assert_eq!(
            pset.clone().decompose(),
            [
                PermutationSet::from_rule(&ir(1, "a,b")),
                PermutationSet::from_rule(&ir(1, "c")),
                PermutationSet::from_rule(&ir(0, "d")),
            ]
            .into(),
        );
        pset.remove(&p([(0, "a"), (1, "b"), (1, "c"), (0, "d")]));
        assert_eq!(
            pset.decompose(),
            [
                PermutationSet::from_rule(&ir(1, "a")),
                PermutationSet::from_rule(&ir(0, "b")),
                PermutationSet::from_rule(&ir(1, "c")),
                PermutationSet::from_rule(&ir(0, "d")),
            ]
            .into(),
        );

        let mut pset = PermutationSet::from_rule(&ir(4, "ab,c,d,ef,g,h"));
        let mut subset1 = PermutationSet::from_rule(&ir(2, "ab,c,d"));
        let mut subset2 = PermutationSet::from_rule(&ir(2, "ef,g,h"));
        for p in pset.permutations.iter().cloned().collect_vec() {
            if !subset1.permutations.iter().any(|sp| p.is_compatible(sp)) {
                pset.remove(&p);
            }
        }
        assert_eq!(
            pset.clone().decompose(),
            [subset1.clone(), subset2.clone()].into(),
        );
        // Decomposed rulesets can still have constrained permutation sets
        let ab2c0d0 = p([(2, "ab"), (0, "c"), (0, "d")]);
        subset1.remove(&ab2c0d0);
        for p in pset.permutations.iter().cloned().collect_vec() {
            if p.is_compatible(&ab2c0d0) {
                pset.remove(&p);
            }
        }
        assert_eq!(
            pset.clone().decompose(),
            [subset1.clone(), subset2.clone()].into(),
        );
        let ef1g0h1 = p([(1, "ef"), (0, "g"), (1, "h")]);
        subset2.remove(&ef1g0h1);
        for p in pset.permutations.iter().cloned().collect_vec() {
            if p.is_compatible(&ef1g0h1) {
                pset.remove(&p);
            }
        }
        assert_eq!(pset.decompose(), [subset1, subset2].into());
    }

    #[test]
    fn test_ruleset_cross_eliminate_and_rereduce() {
        macro_rules! compare {
            (
                $rules:expr;
                $(output => $output:expr)?;
                $(rereduced => $rereduced:expr)?
            ) => {{
                use frozenset::Freeze;
                let mut ruleset = PermutedRuleset::new($rules.into());
                ruleset.cross_eliminate().expect("cross_eliminate failed");
                $(
                    assert_eq!(
                        ruleset
                            .permu_map
                            .values()
                            .map(|ps| ps.permutations.clone().freeze())
                            .collect::<HashSet<_>>(),
                        $output.into_iter().map(|perms| perms.into()).collect(),
                    );
                )?
                ruleset.rereduce().expect("rereduce failed");
                $(
                    assert_eq!(
                        ruleset
                            .permu_map
                            .values()
                            .map(|ps| ps.permutations.clone().freeze())
                            .collect::<HashSet<_>>(),
                        $rereduced.into_iter().map(|perms| perms.into()).collect(),
                    );
                )?
            }};
            ($rules:expr, None $(, $rereduced:expr)? $(,)?) => {
                compare!($rules; ; $(rereduced => $rereduced)?)
            };
            ($rules:expr, $output:expr $(, $rereduced:expr)? $(,)?) => {
                compare!($rules; output => $output; $(rereduced => $rereduced)?)
            };
        }

        // Rules constrained due to overlap
        compare!(
            [ir(1, "a,b,c"), ir(2, "b,c,d")],
            [
                [
                    p([(0, "a"), (1, "b"), (0, "c")]),
                    p([(0, "a"), (0, "b"), (1, "c")]),
                ],
                [
                    p([(1, "b"), (0, "c"), (1, "d")]),
                    p([(0, "b"), (1, "c"), (1, "d")]),
                ],
            ],
            [
                HashSet::from([p([(0, "a")])]),
                HashSet::from([p([(1, "b"), (0, "c")]), p([(0, "b"), (1, "c")])]),
                HashSet::from([p([(1, "d")])]),
            ],
        );

        // Constraining causes further cascade
        compare!(
            [
                ir(2, "a,b,c"),
                ir(1, "b,c,d"),
                ir(1, "c,d,e"),
                ir(1, "d,e,f"),
                ir(1, "e,f,g"),
            ],
            [
                [
                    p([(1, "a"), (1, "b"), (0, "c")]),
                    p([(1, "a"), (0, "b"), (1, "c")])
                ],
                [
                    p([(1, "b"), (0, "c"), (0, "d")]),
                    p([(0, "b"), (1, "c"), (0, "d")])
                ],
                [
                    p([(1, "c"), (0, "d"), (0, "e")]),
                    p([(0, "c"), (0, "d"), (1, "e")])
                ],
                [
                    p([(0, "d"), (1, "e"), (0, "f")]),
                    p([(0, "d"), (0, "e"), (1, "f")])
                ],
                [
                    p([(1, "e"), (0, "f"), (0, "g")]),
                    p([(0, "e"), (1, "f"), (0, "g")]),
                ],
            ],
            [
                HashSet::from([p([(1, "a")])]),
                HashSet::from([p([(1, "b"), (0, "c")]), p([(0, "b"), (1, "c")])]),
                HashSet::from([p([(1, "c"), (0, "e")]), p([(0, "c"), (1, "e")])]),
                HashSet::from([p([(0, "d")])]),
                HashSet::from([p([(1, "e"), (0, "f")]), p([(0, "e"), (1, "f")])]),
                HashSet::from([p([(0, "g")])]),
            ],
        );

        // Rule loop determines all mines (in a way that reduce_rules could not)
        compare!(
            [
                ir(2, "a,b,c,s,t"),
                ir(2, "b,c,d"),
                ir(2, "c,d,e"),
                ir(2, "d,e,f,g,h"),
                ir(2, "g,h,i"),
                ir(2, "h,i,j"),
                ir(2, "i,j,k,l,m"),
                ir(2, "l,m,n"),
                ir(2, "m,n,o"),
                ir(2, "n,o,p,q,r"),
                ir(2, "q,r,s"),
                ir(2, "r,s,t"),
            ],
            [
                [p([(0, "a"), (0, "b"), (1, "c"), (1, "s"), (0, "t")])],
                [p([(0, "b"), (1, "c"), (1, "d")])],
                [p([(1, "c"), (1, "d"), (0, "e")])],
                [p([(1, "d"), (0, "e"), (0, "f"), (0, "g"), (1, "h")])],
                [p([(0, "g"), (1, "h"), (1, "i")])],
                [p([(1, "h"), (1, "i"), (0, "j")])],
                [p([(1, "i"), (0, "j"), (0, "k"), (0, "l"), (1, "m")])],
                [p([(0, "l"), (1, "m"), (1, "n")])],
                [p([(1, "m"), (1, "n"), (0, "o")])],
                [p([(1, "n"), (0, "o"), (0, "p"), (0, "q"), (1, "r")])],
                [p([(0, "q"), (1, "r"), (1, "s")])],
                [p([(1, "r"), (1, "s"), (0, "t")])],
            ],
            [
                HashSet::from([p([(0, "a")])]),
                HashSet::from([p([(0, "b")])]),
                HashSet::from([p([(1, "c")])]),
                HashSet::from([p([(1, "d")])]),
                HashSet::from([p([(0, "e")])]),
                HashSet::from([p([(0, "f")])]),
                HashSet::from([p([(0, "g")])]),
                HashSet::from([p([(1, "h")])]),
                HashSet::from([p([(1, "i")])]),
                HashSet::from([p([(0, "j")])]),
                HashSet::from([p([(0, "k")])]),
                HashSet::from([p([(0, "l")])]),
                HashSet::from([p([(1, "m")])]),
                HashSet::from([p([(1, "n")])]),
                HashSet::from([p([(0, "o")])]),
                HashSet::from([p([(0, "p")])]),
                HashSet::from([p([(0, "q")])]),
                HashSet::from([p([(1, "r")])]),
                HashSet::from([p([(1, "s")])]),
                HashSet::from([p([(0, "t")])]),
            ],
        );

        // Impossible configurations
        let mut ruleset = PermutedRuleset::new(
            [
                ir(1, "a,b,c"),
                ir(2, "b,c,d"),
                ir(2, "a,b,d"),
                ir(2, "a,c,d"),
            ]
            .into(),
        );
        ruleset.cross_eliminate().expect_err("Should be impossible");
        ruleset = PermutedRuleset::new([ir(1, "a,b,c,d"), ir(3, "b,c,d,e")].into());
        ruleset.cross_eliminate().expect_err("Should be impossible");

        // More complex re-reductions
        compare!(
            [ir(2, "a,b,c,d"), ir(1, "a,b,x"), ir(1, "c,d,y"),],
            None,
            [
                HashSet::from([p([(1, "a"), (0, "b")]), p([(0, "a"), (1, "b")])]),
                HashSet::from([p([(1, "c"), (0, "d")]), p([(0, "c"), (1, "d")])]),
                HashSet::from([p([(0, "x")])]),
                HashSet::from([p([(0, "y")])]),
            ],
        );
        compare!(
            [
                ir(3, "a,b,c,d,e,f"),
                ir(1, "e,f,y"),
                ir(2, "a,b,c,d,x"),
                ir(1, "x,k,l"),
                ir(2, "k,l,m"),
                ir(1, "b,c,q"),
            ],
            None,
            [
                HashSet::from([
                    p([(1, "a"), (1, "b"), (0, "c"), (0, "d")]),
                    p([(1, "a"), (0, "b"), (1, "c"), (0, "d")]),
                    p([(1, "a"), (0, "b"), (0, "c"), (1, "d")]),
                    p([(0, "a"), (1, "b"), (0, "c"), (1, "d")]),
                    p([(0, "a"), (0, "b"), (1, "c"), (1, "d")])
                ]),
                HashSet::from([
                    p([(1, "b"), (0, "c"), (0, "q")]),
                    p([(0, "b"), (1, "c"), (0, "q")]),
                    p([(0, "b"), (0, "c"), (1, "q")])
                ]),
                HashSet::from([p([(1, "e"), (0, "f")]), p([(0, "e"), (1, "f")])]),
                HashSet::from([p([(1, "k"), (0, "l")]), p([(0, "k"), (1, "l")])]),
                HashSet::from([p([(0, "x")])]),
                HashSet::from([p([(0, "y")])]),
                HashSet::from([p([(1, "m")])]),
            ],
        );
    }

    #[test]
    fn test_partition() {
        // TODO basic cases

        let ruleset = permute_and_interfere(
            [
                ir(3, "a,b,c,d,e,f"),
                ir(1, "e,f,y"),
                ir(2, "a,b,c,d,x"),
                ir(1, "x,k,l"),
                ir(2, "k,l,m"),
                ir(1, "b,c,q"),
            ]
            .into(),
        )
        .expect("permute_and_interfere should succeed");
        let fronts = ruleset.split_fronts();
        assert_eq!(
            fronts
                .into_iter()
                .map(|ruleset| {
                    ruleset
                        .permu_map
                        .into_values()
                        .map(|ps| ps.permutations.freeze())
                        .collect::<FrozenSet<_>>()
                })
                .collect::<FrozenSet<_>>(),
            [
                FrozenSet::from([
                    FrozenSet::from([
                        p([(1, "a"), (1, "b"), (0, "c"), (0, "d")]),
                        p([(1, "a"), (0, "b"), (1, "c"), (0, "d")]),
                        p([(1, "a"), (0, "b"), (0, "c"), (1, "d")]),
                        p([(0, "a"), (1, "b"), (0, "c"), (1, "d")]),
                        p([(0, "a"), (0, "b"), (1, "c"), (1, "d")])
                    ]),
                    FrozenSet::from([
                        p([(1, "b"), (0, "c"), (0, "q")]),
                        p([(0, "b"), (1, "c"), (0, "q")]),
                        p([(0, "b"), (0, "c"), (1, "q")])
                    ]),
                ]),
                FrozenSet::from([FrozenSet::from([
                    p([(1, "e"), (0, "f")]),
                    p([(0, "e"), (1, "f")])
                ])]),
                FrozenSet::from([FrozenSet::from([
                    p([(1, "k"), (0, "l")]),
                    p([(0, "k"), (1, "l")])
                ])]),
                FrozenSet::from([FrozenSet::from([p([(0, "x")])])]),
                FrozenSet::from([FrozenSet::from([p([(0, "y")])])]),
                FrozenSet::from([FrozenSet::from([p([(1, "m")])])]),
            ]
            .into(),
        );
    }

    // enumerate
    // trivial front?

    #[test]
    fn test_uncharted_cell() {
        let c = UnchartedCell::new(0);
        assert_eq!(c.len(), 0);
        assert_eq!(c.iter().collect_vec(), vec![]);
        let c = UnchartedCell::new(50);
        assert_eq!(c.len(), 50);
        assert_eq!(c.iter().collect_vec(), vec![()]);
    }
}
