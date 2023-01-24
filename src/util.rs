use std::cmp::min;
use std::collections::{HashMap, HashSet};

use crate::{BoardInfo, Rule};

/// A cell on the board
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum BoardCell {
    /// A cell that has been revealed and is empty
    Empty(usize),
    /// A cell that is known to be a mine
    Mine,
    /// A cell that is completely unknown
    Unknown,
}

/// Simple representation of a game board (no game logic!)
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Board {
    /// The cells of the board
    cells: HashMap<(usize, usize), BoardCell>,
    /// The width of the board
    width: usize,
    /// The height of the board
    height: usize,
}
impl Board {
    /// Create a game board from an ASCII-encoded description, where:
    /// - `*` is a mine
    /// - `x` is an unknown cell
    /// - `0`-`8` is a revealed cell with that many adjacent mines
    /// - `.` can be used in place of `0`
    /// - Trailing or leading whitespace is ignored
    ///
    /// # Errors
    ///
    /// If the board is not rectangular, or has a width or height of 0, an error
    /// is returned.
    pub fn new(encoded: &str) -> Result<Self, String> {
        let lines = encoded.trim().lines().map(|l| l.trim()).collect::<Vec<_>>();
        let height = lines.len();
        if height == 0 {
            return Err("Board must have at least one row".to_string());
        }
        let width = lines[0].len();
        if width == 0 {
            return Err("Board must have at least one column".to_string());
        }
        if let Some(line) = lines.iter().find(|l| l.len() != width) {
            return Err(format!(
                concat!(
                    "Board must be rectangular (found line with length {},",
                    " expected length {})",
                ),
                line.len(),
                width,
            ));
        }
        let mut cells = HashMap::new();
        for (row, line) in lines.into_iter().enumerate() {
            for (col, c) in line.chars().enumerate() {
                cells.insert(
                    (row, col),
                    match c {
                        '*' => BoardCell::Mine,
                        'x' => BoardCell::Unknown,
                        '.' => BoardCell::Empty(0),
                        n @ '1'..='8' => {
                            BoardCell::Empty(
                                n.to_digit(10).expect(
                                    "n has been validated to be a decimal digit",
                                ) as usize,
                            )
                        },
                        _ => {
                            return Err(format!(
                                "Invalid character '{}' at ({}, {})",
                                c, row, col
                            ));
                        },
                    },
                );
            }
        }
        Ok(Self {
            cells,
            width,
            height,
        })
    }

    /// Get a list of cells adjacent to the given cell
    pub fn adjacent(
        &self,
        (row, col): (usize, usize),
    ) -> Vec<((usize, usize), BoardCell)> {
        let mut adjacent = Vec::new();
        for r in row.saturating_sub(1)..=min(row + 1, self.height - 1) {
            for c in col.saturating_sub(1)..=min(col + 1, self.width - 1) {
                if r == row && c == col {
                    continue;
                }
                adjacent.push(((r, c), self.cells[&(r, c)]));
            }
        }
        adjacent
    }

    pub fn cell_name(&self, (row, col): (usize, usize)) -> String {
        format!(
            "{0:01$}-{2:03$}",
            row,
            self.height.to_string().len(),
            col,
            self.width.to_string().len()
        )
    }

    pub fn total_cells(&self) -> usize {
        self.width * self.height
    }

    /// Reference algorithm for generating input rules and baord info from a
    /// game state.
    ///
    /// `everything_mode`: If `false`, only include 'interesting' rules i.e.
    /// omit the parts of the board that have already been solved. If `true`,
    /// include rules to completely describe the state of the board (but still
    /// don't include *every* possible rule, as this would include a huge number
    /// of degenerate / redundant rules). In general, invalid boards will only
    /// be detected by everything mode.
    ///
    /// In 'interesting mode':
    /// - Create a rule for each 'number' cell that borders an uncovered cell
    /// - Create a rule encompassing cells with known mines, including *only*
    ///   those cells which are referenced by the rules from the previous step
    /// In everything mode:
    /// - Create a rule for each 'number' cell
    /// - Create a rule encompassing all known mines
    /// - Create a rule encompassing all unknown cells
    /// - Create a rule for all cells adjacent to blank/empty cells, and not
    ///   included in the previous rule. Thus, this rule will only be present
    ///   for invalid boards or boards whose empty areas have not been fully
    ///   expanded.
    pub fn generate_rules(
        &self,
        total_mines: usize,
        everything_mode: bool,
    ) -> (Vec<Rule<(usize, usize)>>, BoardInfo) {
        /// Rule-building helper; don't create degenerate rules
        ///
        /// Allows mines > cells, such as in the event of an invalid board
        fn rule(
            mines: usize,
            cells: impl IntoIterator<Item = (usize, usize)>,
        ) -> Option<Rule<(usize, usize)>> {
            let mut iter = cells.into_iter();
            let next = iter.next();
            if mines != 0 || next.is_some() {
                Some(Rule::new(mines, iter.chain(next)))
            } else {
                None
            }
        }

        let mut clear_cells = HashSet::new();
        let mut zero_cells = HashSet::new();
        let mut relevant_mines = HashSet::new();
        let mut num_known_mines = 0;

        let mut rules = Vec::new();
        for (&cell_id, &cell) in self.cells.iter() {
            if cell == BoardCell::Mine {
                num_known_mines += 1;
                if everything_mode {
                    relevant_mines.insert(cell_id);
                }
            } else if let BoardCell::Empty(adj) = cell {
                clear_cells.insert(cell_id);
                let neighbours = self.adjacent(cell_id);
                if adj > 0 {
                    if everything_mode
                        || neighbours.iter().any(|&(_, c)| c == BoardCell::Mine)
                    {
                        rules.extend(rule(
                            adj,
                            neighbours
                                .iter()
                                .copied()
                                .filter(|&(_, nc)| {
                                    nc == BoardCell::Mine || nc == BoardCell::Unknown
                                })
                                .map(|(id, _)| id),
                        ));
                        relevant_mines.extend(
                            neighbours
                                .into_iter()
                                .filter(|&(_, c)| c == BoardCell::Mine)
                                .map(|(id, _)| id),
                        );
                    }
                } else {
                    zero_cells.extend(neighbours.into_iter().map(|(id, _)| id));
                }
            }
        }

        let num_irrelevant_mines = num_known_mines - relevant_mines.len();
        let board_info = BoardInfo {
            total_cells: self.total_cells()
                - (if everything_mode {
                    0
                } else {
                    clear_cells.len() + num_irrelevant_mines
                }),
            total_mines: total_mines
                - if everything_mode {
                    0
                } else {
                    num_irrelevant_mines
                },
        };

        rules.extend(rule(relevant_mines.len(), relevant_mines));
        if everything_mode {
            rules.extend(rule(0, zero_cells.difference(&clear_cells).copied()));
            rules.extend(rule(0, clear_cells));
        }

        (rules, board_info)
    }
}

/// See [`Board::new`] and [`Board::generate_rules`]. Turns an ASCII-art board
/// into a list of rules and board info.
pub fn read_board(
    encoded: &str,
    total_mines: usize,
    everything_mode: bool,
) -> Result<(Vec<Rule<(usize, usize)>>, BoardInfo), String> {
    let board = Board::new(encoded)?;
    Ok(board.generate_rules(total_mines, everything_mode))
}
