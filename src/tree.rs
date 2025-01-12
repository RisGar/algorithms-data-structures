#[allow(dead_code)]
/// Different traversal techniques for trees.
pub enum Order {
  Pre,
  In,
  Post,
}

#[allow(dead_code)]
/// Generic Tree
pub trait Tree<T> {
  fn new() -> Self;
  /// Insert a value into the tree, returns `true` if the value is not already in the tree.
  fn insert(&mut self, val: T) -> bool;
  /// Removes a value in tree, returns `true` if the value was found.
  fn remove(&mut self, val: T) -> bool;
  /// Whether a tree contains a specific value.
  fn has(&self, val: T) -> bool;
  /// Number of elements in a tree.
  fn len(&self) -> usize;
  /// List representation of a tree in different traversal techniques.
  fn to_list(&self, order: Order) -> Vec<T>;
}
