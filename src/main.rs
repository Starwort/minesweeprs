use minesweeprs::{solve, BoardInfo, Rule};
fn main() {
    let solved = solve(
        &[
            Rule::new(1, ['A', 'B'].into_iter()),
            Rule::new(2, ['A', 'B', 'C'].into_iter()),
            Rule::new(3, ['B', 'C', 'D'].into_iter()),
            Rule::new(2, ['C', 'D', 'E'].into_iter()),
            Rule::new(2, ['D', 'E', 'F', 'G', 'H'].into_iter()),
            Rule::new(1, ['G', 'H', 'I'].into_iter()),
            Rule::new(1, ['H', 'I'].into_iter()),
        ],
        BoardInfo {
            total_cells: 85,
            total_mines: 10,
        },
        '.',
    );
    println!("Solution: {solved:#?}");
}
