# Minesweeprs

This project is a port of [a minesweeper solver algorithm by @mrgriscom](https://github.com/mrgriscom/minesweepr). It is written in Rust and aims to improve performance compared to the original, and allow it to run in-browser via WebAssembly.

## Solving

To solve a board, you provide a number of abstract 'rules' describing the game state, along with information about the board as a whole: total number of cells and total number of mines. The original project's 'cell mine probability' feature is also implemented, but does not have the same level of support.

Each rule represents information gleaned from the uncovered cells of the board. A single `Rule` consists of a set of cells, along with how many mines are to be found among that set. So for a given uncovered cell (say we uncovered a 3), we'd generate: `Rule::new(3, [set of cells adjacent to the uncovered cell])`.

*The solver does **not** have any concept of a grid, or the board's geometry. It just knows about specific sets of cells.*

Here's an example (ASCII art taken from the original README):

```text
..1Axxxxxx
..2Bxxxxxx
..3Cxxxxxx
..2Dxxxxxx
112Exxxxxx
IHGFxxxxxx
xxxxxxxxxx
xxxxxxxxxx
xxxxxxxxxx
xxxxxxxxxx
```

This is an easy-mode board; 10x10, with 10 mines. We've assigned a unique tag (`A`, `B`, `C`, ...) to each covered cell next to the uncovered region (henceforth referred to as a 'front' of play).

This board can be solved with the following code:

```rust
use std::rc::Rc;
use minesweeprs::{solve, BoardInfo, Rule};
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
    BoardInfo { total_cells: 85, total_mines: 10 },
    '.',
);
// The board is solvable, so the below should hold:
assert_eq!(
    output,
    Ok(
        [
            ('A', 0.0),
            ('B', 1.0),
            ('C', 1.0),
            ('D', 1.0),
            ('E', 0.0),
            ('F', 0.07792207792207793),
            ('G', 0.0),
            ('H', 0.9220779220779222),
            ('I', 0.07792207792207793),
            ('.', 0.07792207792207792),
        ].into(),
    )
);
```

which will return a `Result<HashMap<char, f64>, InconsistencyError>` - a map of tags to probabilities. The `Result` will be `Ok` if the board is solvable, and `Err` if it is not (e.g. if the state is inconsistent/contradictory, or there is no possible solution).

(although the keys will be in a random order)

From this we see that `B`, `C`, and `D` are guaranteed to be mines, `A`, `E`, and `G` are guaranteed to be safe, `H` is 92.21% likely to be a mine, and `F`, `I`, and all other cells (represented by the tag `.`) are all 7.79% likely to be mines.

Note that `total_cells` was passed as 85 instead of 100. This is because 15 cells are uncovered, and were not included in any rule. The solver does not know anything about the geometry of the grid, so these cells are simply subtracted from the total number of cells and the solver never even needs to know they exist. Alternatively, there could be a rule `Rule::new(0, [set of all uncovered cells])` and set `total_cells` to 100. Technically, we could make a separate `Rule` for every single uncovered cell, but that is cumbersome and inefficient.

In general, `total_cells` must equal the number of all covered cells in the grid, plus the number of uncovered cells that happen to be included in a rule. `total_mines` must equal the total number of mines in the grid, minus any mines that have been identified and *not* mentioned in any `Rule` (or the solver will try to place them in uncovered cells!).

You can see that the specific logic for generating the appropriate arguments to `solve()` is quite nuanced (assuming you don't take the naive route). Luckily, utility code is provided that can do the processing for you. See `minesweepr::util::Board::generate_rules()`. You can also use `minesweepr::util::read_board()` (without the explicit tagging `A`, `B`, `C` that was done above for illustrative purposes).

## Interactive demo (FUTURE FEATURE)

An interactive player is [will be] provided in `web_demo/` as a simple web app. All game logic and rendering is client-side JavaScript; board solving is done via WebAssembly and a web worker (to avoid freezing the UI thread).

## Future work

In the future, I'd like to find a way to optimise out as many of the uses of clone as possible, ideally ending with zero-clone data structures. This would improve performance, possibly significantly. I'm not sure if this is possible, but perhaps someone with more experience optimising allocations could help with this.

Additionally, I would like to reduce or remove the reliance on the nightly compiler. This is currently required for the features `generators` and `generator_trait`. These features are used to create Python-style generator iterators. Removing these generators without introducing boxed iterators would probably require a significant amount of boilerplate, so I'm not sure if it's worth it.
