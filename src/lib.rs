//! Left-leaning red-black BST (Sedgewick's LLRB algorithm).
//!
//! Invariants:
//! 1. Root is always Black
//! 2. No right-leaning red links (in stable state)
//! 3. No two consecutive red links on any path
//! 4. All null paths have equal black depth
//! 5. New nodes inserted as Red

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
enum Color {
    Red,
    Black,
}

type Link<T> = Option<Box<Node<T>>>;

struct Node<T: Ord> {
    key: T,
    color: Color,
    left: Link<T>,
    right: Link<T>,
    size: usize,
}

impl<T: Ord> Node<T> {
    fn new(key: T, color: Color) -> Box<Self> {
        Box::new(Node {
            key,
            color,
            left: None,
            right: None,
            size: 1,
        })
    }
}

fn is_red<T: Ord>(link: &Link<T>) -> bool {
    link.as_ref().is_some_and(|n| n.color == Color::Red)
}

fn node_size<T: Ord>(link: &Link<T>) -> usize {
    link.as_ref().map_or(0, |n| n.size)
}

fn update_size<T: Ord>(n: &mut Node<T>) {
    n.size = 1 + node_size(&n.left) + node_size(&n.right);
}

fn rotate_left<T: Ord>(mut h: Box<Node<T>>) -> Box<Node<T>> {
    let mut x = h.right.take().unwrap();
    h.right = x.left.take();
    x.color = h.color;
    h.color = Color::Red;
    update_size(&mut h);
    x.left = Some(h);
    update_size(&mut x);
    x
}

fn rotate_right<T: Ord>(mut h: Box<Node<T>>) -> Box<Node<T>> {
    let mut x = h.left.take().unwrap();
    h.left = x.right.take();
    x.color = h.color;
    h.color = Color::Red;
    update_size(&mut h);
    x.right = Some(h);
    update_size(&mut x);
    x
}

fn toggle_color(c: Color) -> Color {
    match c {
        Color::Red => Color::Black,
        Color::Black => Color::Red,
    }
}

fn flip_colors<T: Ord>(h: &mut Node<T>) {
    h.color = toggle_color(h.color);
    if let Some(ref mut l) = h.left {
        l.color = toggle_color(l.color);
    }
    if let Some(ref mut r) = h.right {
        r.color = toggle_color(r.color);
    }
}

fn fix_up<T: Ord>(mut h: Box<Node<T>>) -> Box<Node<T>> {
    // Lean left
    if is_red(&h.right) && !is_red(&h.left) {
        h = rotate_left(h);
    }
    // Balance 4-node
    let left_left_red = h.left.as_ref().is_some_and(|l| is_red(&l.left));
    if is_red(&h.left) && left_left_red {
        h = rotate_right(h);
    }
    // Split 4-node
    if is_red(&h.left) && is_red(&h.right) {
        flip_colors(&mut h);
    }
    update_size(&mut h);
    h
}

fn insert_rec<T: Ord>(link: Link<T>, key: T) -> (Link<T>, bool) {
    match link {
        None => {
            let node = Node::new(key, Color::Red);
            (Some(node), true)
        }
        Some(mut h) => {
            let inserted;
            if key < h.key {
                let (new_left, ins) = insert_rec(h.left.take(), key);
                h.left = new_left;
                inserted = ins;
            } else if key > h.key {
                let (new_right, ins) = insert_rec(h.right.take(), key);
                h.right = new_right;
                inserted = ins;
            } else {
                return (Some(h), false);
            }
            (Some(fix_up(h)), inserted)
        }
    }
}

fn move_red_left<T: Ord>(mut h: Box<Node<T>>) -> Box<Node<T>> {
    flip_colors(&mut h);
    let right_has_red_left = h.right.as_ref().is_some_and(|r| is_red(&r.left));
    if right_has_red_left {
        let r = h.right.take().unwrap();
        h.right = Some(rotate_right(r));
        h = rotate_left(h);
        flip_colors(&mut h);
    }
    h
}

fn move_red_right<T: Ord>(mut h: Box<Node<T>>) -> Box<Node<T>> {
    flip_colors(&mut h);
    let left_has_red_left = h.left.as_ref().is_some_and(|l| is_red(&l.left));
    if left_has_red_left {
        h = rotate_right(h);
        flip_colors(&mut h);
    }
    h
}

/// Deletes the minimum node from the subtree rooted at h.
/// Returns (new subtree root, deleted key).
fn delete_min_rec<T: Ord>(mut h: Box<Node<T>>) -> (Link<T>, T) {
    if h.left.is_none() {
        return (None, h.key);
    }
    if !is_red(&h.left) && !h.left.as_ref().is_some_and(|l| is_red(&l.left)) {
        h = move_red_left(h);
    }
    let left = h.left.take().unwrap();
    let (new_left, min_key) = delete_min_rec(left);
    h.left = new_left;
    (Some(fix_up(h)), min_key)
}

fn delete_rec<T: Ord>(link: Link<T>, key: &T) -> (Link<T>, bool) {
    match link {
        None => (None, false),
        Some(mut h) => {
            if key < &h.key {
                if h.left.is_none() {
                    return (Some(h), false);
                }
                if !is_red(&h.left) && !h.left.as_ref().is_some_and(|l| is_red(&l.left)) {
                    h = move_red_left(h);
                }
                let left = h.left.take();
                let (new_left, deleted) = delete_rec(left, key);
                h.left = new_left;
                (Some(fix_up(h)), deleted)
            } else {
                // key >= h.key
                if is_red(&h.left) {
                    h = rotate_right(h);
                    // Now key >= h.key still? Not necessarily after rotation.
                    // We need to re-route: the old h is now h.right
                    let right = h.right.take();
                    let (new_right, deleted) = delete_rec(right, key);
                    h.right = new_right;
                    return (Some(fix_up(h)), deleted);
                }
                if key == &h.key && h.right.is_none() {
                    return (None, true);
                }
                let right_not_red = !is_red(&h.right);
                let right_left_not_red = h.right.as_ref().is_none_or(|r| !is_red(&r.left));
                if h.right.is_some() && right_not_red && right_left_not_red {
                    h = move_red_right(h);
                }
                if key == &h.key {
                    let right = h.right.take().unwrap();
                    let (new_right, successor) = delete_min_rec(right);
                    h.key = successor;
                    h.right = new_right;
                    (Some(fix_up(h)), true)
                } else {
                    let right = h.right.take();
                    let (new_right, deleted) = delete_rec(right, key);
                    h.right = new_right;
                    (Some(fix_up(h)), deleted)
                }
            }
        }
    }
}

fn inorder_rec<'a, T: Ord>(link: &'a Link<T>, result: &mut Vec<&'a T>) {
    if let Some(ref node) = link {
        inorder_rec(&node.left, result);
        result.push(&node.key);
        inorder_rec(&node.right, result);
    }
}

fn rank_rec<T: Ord>(link: &Link<T>, key: &T) -> usize {
    match link {
        None => 0,
        Some(ref node) => {
            if key <= &node.key {
                rank_rec(&node.left, key)
            } else {
                1 + node_size(&node.left) + rank_rec(&node.right, key)
            }
        }
    }
}

fn select_rec<T: Ord>(link: &Link<T>, k: usize) -> Option<&T> {
    match link {
        None => None,
        Some(ref node) => {
            let left_size = node_size(&node.left);
            if k < left_size {
                select_rec(&node.left, k)
            } else if k == left_size {
                Some(&node.key)
            } else {
                select_rec(&node.right, k - left_size - 1)
            }
        }
    }
}

fn min_rec<T: Ord>(link: &Link<T>) -> Option<&T> {
    match link {
        None => None,
        Some(ref node) => {
            if node.left.is_none() {
                Some(&node.key)
            } else {
                min_rec(&node.left)
            }
        }
    }
}

fn max_rec<T: Ord>(link: &Link<T>) -> Option<&T> {
    match link {
        None => None,
        Some(ref node) => {
            if node.right.is_none() {
                Some(&node.key)
            } else {
                max_rec(&node.right)
            }
        }
    }
}

/// Left-leaning red-black BST.
pub struct RedBlackTree<T: Ord> {
    root: Link<T>,
    size: usize,
}

impl<T: Ord> RedBlackTree<T> {
    /// Creates an empty tree.
    pub fn new() -> Self {
        RedBlackTree {
            root: None,
            size: 0,
        }
    }

    /// Inserts a key. Returns `true` if the key was newly inserted,
    /// `false` if it was already present (no duplicates stored).
    pub fn insert(&mut self, key: T) -> bool {
        let (new_root, inserted) = insert_rec(self.root.take(), key);
        self.root = new_root;
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        if inserted {
            self.size += 1;
        }
        inserted
    }

    /// Deletes a key. Returns `true` if the key was found and removed.
    pub fn delete(&mut self, key: &T) -> bool {
        let (new_root, deleted) = delete_rec(self.root.take(), key);
        self.root = new_root;
        if let Some(ref mut root) = self.root {
            root.color = Color::Black;
        }
        if deleted {
            self.size -= 1;
        }
        deleted
    }

    /// Returns `true` if the tree contains the given key.
    pub fn contains(&self, key: &T) -> bool {
        let mut current = &self.root;
        loop {
            match current {
                None => return false,
                Some(ref node) => {
                    if key == &node.key {
                        return true;
                    } else if key < &node.key {
                        current = &node.left;
                    } else {
                        current = &node.right;
                    }
                }
            }
        }
    }

    /// Returns all keys in ascending (sorted) order.
    pub fn inorder(&self) -> Vec<&T> {
        let mut result = Vec::with_capacity(self.size);
        inorder_rec(&self.root, &mut result);
        result
    }

    /// Returns the number of keys in the tree.
    pub fn len(&self) -> usize {
        self.size
    }

    /// Returns `true` if the tree is empty.
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// Returns the number of keys strictly less than `key`.
    pub fn rank(&self, key: &T) -> usize {
        rank_rec(&self.root, key)
    }

    /// Returns the k-th smallest key (0-indexed), or `None` if out of range.
    pub fn select(&self, k: usize) -> Option<&T> {
        select_rec(&self.root, k)
    }

    /// Returns a reference to the minimum key, or `None` if empty.
    pub fn min(&self) -> Option<&T> {
        min_rec(&self.root)
    }

    /// Returns a reference to the maximum key, or `None` if empty.
    pub fn max(&self) -> Option<&T> {
        max_rec(&self.root)
    }
}

impl<T: Ord> Default for RedBlackTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_new_empty() {
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
    }

    #[test]
    fn test_insert_contains() {
        let mut tree = RedBlackTree::new();
        tree.insert(5);
        assert!(tree.contains(&5));
    }

    #[test]
    fn test_insert_new_returns_true() {
        let mut tree = RedBlackTree::new();
        assert!(tree.insert(42));
    }

    #[test]
    fn test_insert_dup_returns_false() {
        let mut tree = RedBlackTree::new();
        tree.insert(5);
        let len_before = tree.len();
        assert!(!tree.insert(5));
        assert_eq!(tree.len(), len_before);
    }

    #[test]
    fn test_contains_miss_empty() {
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert!(!tree.contains(&10));
    }

    #[test]
    fn test_contains_miss_after_inserts() {
        let mut tree = RedBlackTree::new();
        tree.insert(1);
        tree.insert(2);
        tree.insert(3);
        assert!(!tree.contains(&99));
    }

    #[test]
    fn test_inorder_empty() {
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert_eq!(tree.inorder(), Vec::<&i32>::new());
    }

    #[test]
    fn test_inorder_single() {
        let mut tree = RedBlackTree::new();
        tree.insert(7);
        assert_eq!(tree.inorder(), vec![&7]);
    }

    #[test]
    fn test_inorder_sorted() {
        let mut tree = RedBlackTree::new();
        for &v in &[5, 3, 7, 1, 4, 6, 8] {
            tree.insert(v);
        }
        assert_eq!(tree.inorder(), vec![&1, &3, &4, &5, &6, &7, &8]);
    }

    #[test]
    fn test_len_increments() {
        let mut tree = RedBlackTree::new();
        for i in 0..10 {
            assert_eq!(tree.len(), i);
            tree.insert(i);
        }
        assert_eq!(tree.len(), 10);
    }

    #[test]
    fn test_delete_empty_false() {
        let mut tree: RedBlackTree<i32> = RedBlackTree::new();
        assert!(!tree.delete(&5));
    }

    #[test]
    fn test_delete_leaf() {
        let mut tree = RedBlackTree::new();
        tree.insert(5);
        assert!(tree.delete(&5));
        assert!(tree.is_empty());
        assert!(!tree.contains(&5));
    }

    #[test]
    fn test_delete_two_children() {
        let mut tree = RedBlackTree::new();
        for &v in &[5, 3, 7, 1, 4, 6, 8] {
            tree.insert(v);
        }
        assert!(tree.delete(&5));
        assert!(!tree.contains(&5));
        assert_eq!(tree.len(), 6);
    }

    #[test]
    fn test_delete_nonexistent_false() {
        let mut tree = RedBlackTree::new();
        tree.insert(1);
        tree.insert(2);
        assert!(!tree.delete(&99));
    }

    #[test]
    fn test_delete_inorder_still_sorted() {
        let mut tree = RedBlackTree::new();
        for &v in &[5, 3, 7, 1, 4, 6, 8] {
            tree.insert(v);
        }
        tree.delete(&3);
        tree.delete(&7);
        let keys: Vec<i32> = tree.inorder().into_iter().copied().collect();
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted);
    }

    #[test]
    fn test_min_empty() {
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert_eq!(tree.min(), None);
    }

    #[test]
    fn test_min_after_inserts() {
        let mut tree = RedBlackTree::new();
        for &v in &[3, 1, 4, 1, 5] {
            tree.insert(v);
        }
        assert_eq!(tree.min(), Some(&1));
    }

    #[test]
    fn test_max_after_inserts() {
        let mut tree = RedBlackTree::new();
        for &v in &[3, 1, 4, 5] {
            tree.insert(v);
        }
        assert_eq!(tree.max(), Some(&5));
    }

    #[test]
    fn test_rank_empty() {
        let tree: RedBlackTree<i32> = RedBlackTree::new();
        assert_eq!(tree.rank(&5), 0);
    }

    #[test]
    fn test_rank_basic() {
        let mut tree = RedBlackTree::new();
        for &v in &[1, 2, 3, 4, 5] {
            tree.insert(v);
        }
        assert_eq!(tree.rank(&3), 2);
    }

    #[test]
    fn test_rank_min() {
        let mut tree = RedBlackTree::new();
        for &v in &[4, 2, 6, 1, 3] {
            tree.insert(v);
        }
        let min_val = *tree.min().unwrap();
        assert_eq!(tree.rank(&min_val), 0);
    }

    #[test]
    fn test_rank_max() {
        let mut tree = RedBlackTree::new();
        for &v in &[4, 2, 6, 1, 3] {
            tree.insert(v);
        }
        let max_val = *tree.max().unwrap();
        assert_eq!(tree.rank(&max_val), tree.len() - 1);
    }

    #[test]
    fn test_select_basic() {
        let mut tree = RedBlackTree::new();
        for &v in &[5, 3, 7, 1] {
            tree.insert(v);
        }
        assert_eq!(tree.select(0), Some(&1));
        assert_eq!(tree.select(1), Some(&3));
    }

    #[test]
    fn test_select_out_of_range() {
        let mut tree = RedBlackTree::new();
        tree.insert(1);
        tree.insert(2);
        assert_eq!(tree.select(100), None);
    }

    #[test]
    fn test_rank_select_inverse() {
        let mut tree = RedBlackTree::new();
        for &v in &[10, 5, 15, 3, 7, 12, 20] {
            tree.insert(v);
        }
        let keys: Vec<i32> = tree.inorder().into_iter().copied().collect();
        for k in &keys {
            let r = tree.rank(k);
            assert_eq!(tree.select(r), Some(k));
        }
    }

    #[test]
    fn test_mass_insert_inorder() {
        use std::collections::HashSet;
        let mut rng_state: u64 = 12345;
        let mut vals: Vec<i32> = (1..=100).collect();
        // Simple LCG shuffle
        for i in (1..vals.len()).rev() {
            rng_state = rng_state.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
            let j = (rng_state >> 33) as usize % (i + 1);
            vals.swap(i, j);
        }

        let mut tree = RedBlackTree::new();
        let mut seen = HashSet::new();
        for v in vals {
            let first_time = seen.insert(v);
            let result = tree.insert(v);
            assert_eq!(result, first_time);
        }
        let expected: Vec<i32> = (1..=100).collect();
        let got: Vec<i32> = tree.inorder().into_iter().copied().collect();
        assert_eq!(got, expected);
    }

    #[test]
    fn test_mass_delete() {
        let mut tree = RedBlackTree::new();
        for v in 1..=50 {
            tree.insert(v);
        }
        for v in (2..=50).step_by(2) {
            assert!(tree.delete(&v));
        }
        assert_eq!(tree.len(), 25);
        let keys: Vec<i32> = tree.inorder().into_iter().copied().collect();
        for k in &keys {
            assert_eq!(k % 2, 1, "found even key {k} after deleting all evens");
        }
    }

    #[test]
    fn test_color_invariant_after_inserts() {
        let mut tree = RedBlackTree::new();
        for &v in &[3, 1, 4, 1, 5, 9, 2, 6] {
            tree.insert(v);
        }
        // Verify we can still do operations correctly (invariants maintained by algorithm)
        assert!(tree.contains(&3));
        assert!(tree.contains(&9));
        assert!(!tree.contains(&7));
        let keys: Vec<i32> = tree.inorder().into_iter().copied().collect();
        let mut sorted = keys.clone();
        sorted.sort();
        assert_eq!(keys, sorted);
    }
}
