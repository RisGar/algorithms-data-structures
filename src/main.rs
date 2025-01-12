mod b_tree;
mod binary_search_tree;
mod tree;

use binary_search_tree::Bst;
use tree::Tree;

fn main() {
  let mut bst = Bst::new();
  bst.insert(5);
  bst.insert(3);
  bst.insert(7);
  bst.insert(6);

  println!("{bst}");
}
