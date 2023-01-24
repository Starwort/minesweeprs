use minesweeprs::util::*;
fn main() {
    let board_str = concat!(
        "..1xxxxxxx\n",
        "..2xxxxxxx\n",
        "..3xxxxxxx\n",
        "..2xxxxxxx\n",
        "112xxxxxxx\n",
        "xxxxxxxxxx\n",
        "xxxxxxxxxx\n",
        "xxxxxxxxxx\n",
        "xxxxxxxxxx\n",
        "xxxxxxxxxx\n",
    );
    let board = Board::new(board_str).unwrap();
    println!("Board: {:#?}", board);
    let rules = board.generate_rules(10, false);
    println!("Rules: {:#?}", rules);
}
