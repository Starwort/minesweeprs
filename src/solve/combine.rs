use std::collections::HashMap;

use itertools::Itertools;

use crate::internal_util::map_reduce;
use crate::solve::{Cell, FrontTally};
use crate::InconsistencyError;

/// Struct that tracks, for a constituent front, how many configurations for
/// each number of mines in the front
#[derive(Debug, Clone)]
struct FrontPerMineTotals {
    /// Number of mines -> Number of configurations
    totals: HashMap<usize, f64>,
}
impl FrontPerMineTotals {
    fn singleton(num_mines: usize, total: f64) -> Self {
        Self {
            totals: [(num_mines, total)].into(),
        }
    }

    /// Get the total number of configurations across all possible numbers
    /// of mines
    fn total_count(&self) -> f64 {
        self.totals.values().sum()
    }

    /// Create a new `FrontPerMineTotals` by multiplying the configuration
    /// counts by a fixed factor
    fn multiply(&self, n: f64) -> Self {
        Self {
            totals: self.totals.iter().map(|(&k, &v)| (k, v * n)).collect(),
        }
    }

    /// Compute an aggregate sum of several mappings
    fn sum<'a>(front_totals: impl Iterator<Item = &'a Self>) -> Self {
        Self {
            totals: map_reduce(
                front_totals,
                |ft| ft.totals.iter().map(|(&k, &v)| (k, v)),
                |vals| vals.into_iter().sum(),
            ),
        }
    }
}

/// Struct that tracks, for a given number of mines in the `CombinedFront`,
/// the `FrontPerMineTotals` corresponding to each constituent front
struct AllFrontsPerMineTotals {
    front_totals: Vec<FrontPerMineTotals>,
}
impl AllFrontsPerMineTotals {
    fn total_count(&self) -> f64 {
        if self.front_totals.is_empty() {
            1.0
        } else {
            // The count should match for each constituent front
            self.front_totals[0].total_count()
        }
    }

    fn null() -> Self {
        Self {
            front_totals: vec![],
        }
    }

    fn singleton(num_mines: usize, total: f64) -> Self {
        Self {
            front_totals: vec![FrontPerMineTotals::singleton(num_mines, total)],
        }
    }

    /// Merge two `AllFrontsPerMineTotals` into one, joining into a single
    /// list and performing necessary cross-multiplication
    fn join_with(&self, other: &Self) -> Self {
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

    /// Sum a list of `AllFrontsPerMineTotals` on a per-constituent-front
    /// basis
    fn sum<'a>(front_sets: impl Iterator<Item = &'a Self>) -> Self {
        let front_sets = front_sets.map(|f| &f.front_totals).collect_vec();
        if front_sets.is_empty() {
            Self {
                front_totals: vec![],
            }
        } else {
            Self {
                front_totals: (0..front_sets[0].len())
                    .map(|i| FrontPerMineTotals::sum(front_sets.iter().map(|f| &f[i])))
                    .collect(),
            }
        }
    }
}

/// A representation of a combinatorial fusing of multiple fronts/tallies.
/// Essentially, track:
///
/// - For a total number of mines in the combined front:
///   - For each constituent front:
///     - Count the total number of configurations for each number of mines in
///       the constituent front
pub struct CombinedFront {
    /// Total number of mines in the combined front -> an
    /// `AllFrontsPerMineTotals` for that number of mines
    totals: HashMap<usize, AllFrontsPerMineTotals>,
}
impl CombinedFront {
    /// Get (min, max) possible number of mines in the combined front
    pub fn min_max_mines(&self) -> (usize, usize) {
        self.totals
            .iter()
            .fold((usize::MAX, usize::MIN), |(min, max), (&k, _)| {
                (min.min(k), max.max(k))
            })
    }

    /// Create an 'empty' `CombinedFront`
    pub fn null() -> Self {
        Self {
            totals: [(0, AllFrontsPerMineTotals::null())].into(),
        }
    }

    /// Build a starter `CombinedFront` using known counts for each number
    /// of mines
    fn from_counts_per_num_mines(
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

    /// Build a starter `CombinedFront` from a `FrontTally`
    pub fn from_tally<T: Cell>(tally: &FrontTally<T>) -> Self {
        Self::from_counts_per_num_mines(
            tally
                .subtallies
                .iter()
                .map(|(&num_mines, subtally)| (num_mines, subtally.total)),
        )
    }

    /// Build a starter `CombinedFront` to represent the 'uncharted cells'
    /// region
    pub fn for_other(
        min_mines: usize,
        max_mines: usize,
        relative_likelihood: impl Fn(usize) -> Result<f64, InconsistencyError>,
    ) -> Result<Self, InconsistencyError> {
        Ok(Self::from_counts_per_num_mines(
            (min_mines..=max_mines)
                .map(|num_mines| Ok((num_mines, relative_likelihood(num_mines)?)))
                .collect::<Result<Vec<_>, _>>()?
                .into_iter(),
        ))
    }

    /// Combine two `CombinedFront`s. Min/max remaining mines represent the
    /// total remaining mines available in all fronts yet to be combined
    /// (excluding 'new'). This helps avoid computing combinations whose
    /// numbers of mines can never add up to the requisite number of board
    /// mines. This is also how we converge to a single total number of
    /// mines upon combining all fronts
    pub fn join_with(
        &self,
        other: &Self,
        min_remaining_mines: usize,
        max_remaining_mines: usize,
        at_large_mines: usize,
    ) -> Self {
        let cross_entries = self
            .totals
            .iter()
            .cartesian_product(other.totals.iter())
            .filter_map(|((&a_num_mines, a_fronts), (&b_num_mines, b_fronts))| {
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
            })
            .collect_vec();
        Self {
            totals: map_reduce(
                cross_entries.into_iter(),
                |kv| [kv].into_iter(),
                |vals| AllFrontsPerMineTotals::sum(vals.iter()),
            ),
        }
    }

    /// Once all fronts are combined, unwrap the objects and return the
    /// underlying counts corresponding to each front
    pub fn collapse(self) -> impl Iterator<Item = HashMap<usize, f64>> {
        assert!(self.totals.len() == 1);
        self.totals
            .into_iter()
            .next()
            .unwrap()
            .1
            .front_totals
            .into_iter()
            .map(|e| e.totals)
    }
}
