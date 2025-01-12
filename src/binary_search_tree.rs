use std::{
  cmp::Ordering,
  fmt::{Debug, Display, Formatter},
};

use crate::tree::{Order, Tree};

#[derive(Debug, Clone)]
struct Node<T: Ord + Debug + Clone> {
  val: T,
  left: SubTree<T>,
  right: SubTree<T>,
}

impl<T: Ord + Debug + Clone> Node<T> {
  fn is_leaf(&self) -> bool {
    self.left.0.is_none() && self.right.0.is_none()
  }
}

#[derive(Debug, Clone)]
struct SubTree<T: Ord + Debug + Clone>(Box<Option<Node<T>>>);

impl<T: Ord + Debug + Clone> SubTree<T> {
  fn new() -> Self {
    SubTree(Box::new(None))
  }

  /// Returns the minimal node of a subtree
  fn minimal_node(&self) -> SubTree<T> {
    let mut current = self.clone();
    while let Some(node) = current.0.as_ref() {
      if node.left.0.is_some() {
        current = node.left.clone();
      } else {
        break;
      }
    }
    current
  }

  fn insert(&mut self, val: T) -> bool {
    if let Some(node) = self.0.as_mut() {
      match val.cmp(&node.val) {
        Ordering::Less => node.left.insert(val),
        Ordering::Greater => node.right.insert(val),
        _ => false,
      }
    } else {
      // Current node does not exist
      self.0.replace(Node {
        val,
        left: Self::new(),
        right: Self::new(),
      });
      true
    }
  }

  fn has(&self, val: &T) -> bool {
    if let Some(node) = self.0.as_ref() {
      match val.cmp(&node.val) {
        Ordering::Less => node.left.has(val),
        Ordering::Greater => node.right.has(val),
        Ordering::Equal => true,
      }
    } else {
      // Current node does not exist
      false
    }
  }

  fn len(&self) -> usize {
    if let Some(node) = self.0.as_ref() {
      1 + node.left.len() + node.right.len()
    } else {
      // Current node does not exist
      0
    }
  }

  fn to_list(&self, order: &Order) -> Vec<T> {
    if let Some(node) = self.0.as_ref() {
      let mut result;

      match order {
        Order::In => {
          result = node.left.to_list(order);
          result.push(node.val.clone());
          result.extend(node.right.to_list(order));
        }
        Order::Pre => {
          result = vec![node.val.clone()];
          result.extend(node.left.to_list(order));
          result.extend(node.right.to_list(order));
        }
        Order::Post => {
          result = node.left.to_list(order);
          result.extend(node.right.to_list(order));
          result.push(node.val.clone());
        }
      }

      result
    } else {
      // Current node does not exist
      Vec::new()
    }
  }

  /// [BST Deletion – Wikipedia](https://en.wikipedia.org/wiki/Binary_search_tree#Deletion)
  fn remove(&mut self, val: &T) -> bool {
    if let Some(node) = self.0.as_mut() {
      match val.cmp(&node.val) {
        Ordering::Less => node.left.remove(val),
        Ordering::Greater => node.right.remove(val),
        Ordering::Equal => {
          // Current node to be removed
          if node.is_leaf() {
            *self = SubTree::new();
          } else if node.right.0.is_none() {
            *self = node.left.clone();
          } else if node.left.0.is_none() {
            *self = node.right.clone();
          } else {
            // Two children

            // The node certainly has a right subtree, so the in-order successor is just the minimal node of that
            let successor = node.right.minimal_node();

            if let Some(successor_node) = successor.0.as_ref() {
              node.val = successor_node.val.clone();
              node.right.remove(&successor_node.val);
            }
          }
          true
        }
      }
    } else {
      // Current node does not exist
      false
    }
  }
}

#[derive(Debug)]
pub struct Bst<T: Ord + Debug + Clone> {
  root: SubTree<T>,
}

#[allow(dead_code)]
impl<T: Ord + Debug + Clone> Tree<T> for Bst<T> {
  fn new() -> Self {
    Self {
      root: SubTree::new(),
    }
  }
  fn insert(&mut self, val: T) -> bool {
    self.root.insert(val)
  }

  fn has(&self, val: T) -> bool {
    self.root.has(&val)
  }

  fn len(&self) -> usize {
    self.root.len()
  }

  fn to_list(&self, order: Order) -> Vec<T> {
    self.root.to_list(&order)
  }

  fn remove(&mut self, val: T) -> bool {
    self.root.remove(&val)
  }
}

impl<T: Ord + Debug + Clone> Display for Bst<T> {
  fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
    write!(f, "{:?}", self.to_list(Order::In))
  }
}

#[cfg(test)]
mod tests {
  use super::Bst;
  use crate::tree::{Order, Tree};

  #[test]
  fn test_has() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(7);
    assert!(bst.has(5));
    assert!(bst.has(3));
    assert!(bst.has(7));
    assert!(!bst.has(4));
  }

  #[test]
  fn test_len() {
    let mut bst = Bst::new();
    assert_eq!(bst.len(), 0);
    bst.insert(5);
    assert_eq!(bst.len(), 1);
    bst.insert(3);
    assert_eq!(bst.len(), 2);
    bst.insert(7);
    assert_eq!(bst.len(), 3);
  }

  #[test]
  fn test_in_order() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(7);
    bst.insert(2);
    bst.insert(4);
    bst.insert(6);
    bst.insert(8);
    assert_eq!(bst.to_list(Order::In), vec![2, 3, 4, 5, 6, 7, 8]);
  }

  #[test]
  fn test_delete_leaf() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(7);
    assert!(bst.remove(3));
    assert_eq!(bst.to_list(Order::In), vec![5, 7]);
  }

  #[test]
  fn test_delete_one_child_left() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(2);
    assert!(bst.remove(3));
    assert_eq!(bst.to_list(Order::In), vec![2, 5]);
  }

  #[test]
  fn test_delete_one_child_right() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(4);
    assert!(bst.remove(3));
    assert_eq!(bst.to_list(Order::In), vec![4, 5]);
  }

  #[test]
  fn test_delete_two_children() {
    let mut bst = Bst::new();
    bst.insert(5);
    bst.insert(3);
    bst.insert(7);
    bst.insert(2);
    bst.insert(4);
    bst.insert(6);
    bst.insert(8);
    assert!(bst.remove(5));
    assert_eq!(bst.to_list(Order::In), vec![2, 3, 4, 6, 7, 8]);
  }
}
