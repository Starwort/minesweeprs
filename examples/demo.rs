use minesweeprs::{solve, BoardInfo, Rule};
fn main() {
    let solved = solve(
        &[
            Rule::new(1, ['A', 'B']),
            Rule::new(2, ['A', 'B', 'C']),
            Rule::new(3, ['B', 'C', 'D']),
            Rule::new(2, ['C', 'D', 'E']),
            Rule::new(2, ['D', 'E', 'F', 'G', 'H']),
            Rule::new(1, ['G', 'H', 'I']),
            Rule::new(1, ['H', 'I']),
        ],
        BoardInfo {
            total_cells: 85,
            total_mines: 10,
        },
        '.',
    );
    println!("Solution: {solved:#?}");
}
