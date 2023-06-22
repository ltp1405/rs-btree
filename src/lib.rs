#![allow(dead_code)]

use std::{mem::{swap, take}, fmt::Display};

trait BtreeNode {
    fn should_split(&self) -> bool;
    fn insert<K: PartialOrd, V>(&mut self, key: &K, val: &V);
}

type Key = u32;
type InteriorVal = (Key, Box<SimpleNode>);

#[derive(Debug, PartialEq, Default)]
pub enum SimpleNode {
    #[default]
    None,
    Interior {
        vals: Vec<InteriorVal>,
        left_child: Option<Box<SimpleNode>>,
    },
    Leaf {
        vals: Vec<Key>,
    },
}

#[derive(Debug)]
enum LeafInsertResult {
    Normal(Box<SimpleNode>),
    Splitted(Key, Box<SimpleNode>, Box<SimpleNode>),
}

#[derive(Debug)]
enum InInsertResult {
    Normal(Box<SimpleNode>),
    Splitted(Key, Box<SimpleNode>, Box<SimpleNode>),
}

#[derive(Debug, PartialEq)]
pub enum Slot {
    /// Represent a slot which is not occupied by a key yet
    Hole(u32),
    /// Represent a slot which is occupied by a key
    Cell(u32),
}

fn node_insert(mut node: Box<SimpleNode>, key: u32) -> LeafInsertResult {
    let slot = node.search(key);
    let hole = match slot {
        Slot::Hole(h) => h,
        Slot::Cell(c) => todo!(),
    };
    let node: Box<SimpleNode> = match *node {
        SimpleNode::Leaf { ref mut vals } => {
            vals.insert(hole as usize, key);
            node
        }
        SimpleNode::Interior {
            mut vals,
            mut left_child,
        } => {
            match vals.get_mut(hole as usize) {
                Some(val) => {
                    let val = take(val);
                    let val_key = val.0;
                    let (split, val) = match node_insert(val.1, key) {
                        LeafInsertResult::Normal(node) => (None, node),
                        LeafInsertResult::Splitted(k, l, r) => (Some((k, l)), r),
                    };
                    swap(&mut (val_key, val), &mut vals[hole as usize]);
                    if let Some(v) = split {
                        vals.insert(hole as usize, v);
                    }
                }
                None => {
                    let val = left_child.take().unwrap();
                    let (split, val) = match node_insert(val, key) {
                        LeafInsertResult::Normal(node) => (None, node),
                        LeafInsertResult::Splitted(k, l, r) => (Some((k, l)), r),
                    };
                    let _ = left_child.insert(val);
                    if let Some(v) = split {
                        vals.push(v);
                    }
                }
            }
            Box::new(SimpleNode::Interior { vals, left_child })
        }
        SimpleNode::None => unreachable!(),
    };
    if node.overflow() {
        let (k, l, r) = node_split(node);
        return LeafInsertResult::Splitted(k, l, r);
    }
    LeafInsertResult::Normal(node)
}

fn node_split(node: Box<SimpleNode>) -> (Key, Box<SimpleNode>, Box<SimpleNode>) {
    match *node {
        SimpleNode::None => unreachable!(),
        SimpleNode::Leaf { vals } => {
            let (l, r) = split_in_half(vals);
            let mid_key = r.first().unwrap().clone();
            let l = Box::new(SimpleNode::Leaf { vals: l });
            let r = Box::new(SimpleNode::Leaf { vals: r });
            (mid_key, l, r)
        }
        SimpleNode::Interior { vals, left_child } => {
            let (l, mid, r) = split_in_half_with_mid(vals);
            let mid_key = mid.0;
            let l = Box::new(SimpleNode::Interior {
                vals: l,
                left_child: Some(mid.1),
            });
            let r = Box::new(SimpleNode::Interior {
                vals: r,
                left_child: Some(left_child.unwrap()),
            });
            (mid_key, l, r)
        }
    }
}

fn split_in_half<T>(vals: Vec<T>) -> (Vec<T>, Vec<T>) {
    let mid = vals.len() / 2;
    let mut l = Vec::new();
    let mut r = Vec::new();
    for (i, item) in vals.into_iter().enumerate() {
        if i < mid {
            l.push(item);
        } else {
            r.push(item);
        }
    }
    (l, r)
}

fn split_in_half_with_mid<T>(vals: Vec<T>) -> (Vec<T>, T, Vec<T>) {
    let mid = vals.len() / 2;
    let mut l = Vec::new();
    let mut r = Vec::new();
    let mut mid_val = None;
    for (i, item) in vals.into_iter().enumerate() {
        if i < mid {
            l.push(item);
        } else if i == mid {
            mid_val = Some(item);
        } else {
            r.push(item);
        }
    }
    (l, mid_val.unwrap(), r)
}

impl SimpleNode {
    fn contain(&self, key: Key) -> bool {
        println!("Search for {:?}", key);
        match self {
            Self::Interior { vals, left_child } => {
                let first = vals.first().unwrap().0;
                if key < first {
                    return vals.first().unwrap().1.contain(key);
                }
                let last = vals.last().unwrap().0;
                if key >= last {
                    return left_child.as_ref().unwrap().contain(key);
                }
                for i in 0..vals.len() {
                    let lo = vals[i].0;
                    let hi = vals[i + 1].0;
                    if key >= lo && key < hi {
                        return vals[0].1.contain(key);
                    }
                }
                false
            }
            Self::Leaf { vals } => match vals.binary_search(&key) {
                Ok(_) => return true,
                Err(_) => return false,
            },
            _ => unreachable!(),
        }
    }

    fn overflow(&self) -> bool {
        let len = match self {
            Self::Interior { vals, left_child } => vals.len(),
            Self::Leaf { vals } => vals.len(),
            _ => unreachable!(),
        };
        len > 3
    }

    fn keys(&self) -> Vec<u32> {
        match self {
            SimpleNode::None => unreachable!(),
            Self::Leaf { vals } => vals.iter().map(|e| *e).collect(),
            Self::Interior {
                vals,
                left_child: _,
            } => vals.iter().map(|(e, _)| *e).collect(),
        }
    }

    fn search(&self, search_key: u32) -> Slot {
        let num_cells = self.keys().len();
        if num_cells == 0 {
            return Slot::Hole(0);
        }
        let mut hi = num_cells;
        let mut lo = 0;
        loop {
            let mid = (lo + hi) / 2;
            let mid_key = self.keys()[mid];
            if search_key < mid_key {
                if mid == 0 {
                    return Slot::Hole(0);
                } else if search_key > self.keys()[mid - 1] {
                    return Slot::Hole(mid as u32);
                }
                hi = mid;
            } else if search_key > mid_key {
                if mid == num_cells - 1 {
                    return Slot::Hole(num_cells as u32);
                }
                lo = mid;
            } else {
                return Slot::Cell(mid as u32);
            }
        }
    }
}

#[derive(Debug)]
struct Btree {
    root: Box<SimpleNode>,
}

impl Btree {
    pub fn new() -> Self {
        Self {
            root: Box::new(SimpleNode::Leaf { vals: vec![] }),
        }
    }

    pub fn insert(&mut self, key: Key) {
        let root = take(&mut self.root);
        self.root = match node_insert(root, key) {
            LeafInsertResult::Normal(node) => node,
            LeafInsertResult::Splitted(k, l, r) => Box::new(SimpleNode::Interior {
                vals: vec![(k, l)],
                left_child: Some(r),
            }),
        }
    }
}

#[cfg(test)]
mod tests {
    use std::mem::{swap, take};

    use crate::{node_insert, node_split, Btree, LeafInsertResult};

    use super::SimpleNode;

    fn tree_sample_2() -> Box<SimpleNode> {
        let leaf1 = Box::new(SimpleNode::Leaf { vals: vec![12] });
        let leaf2 = Box::new(SimpleNode::Leaf { vals: vec![98] });
        let leaf3 = Box::new(SimpleNode::Leaf {
            vals: vec![101, 123, 145, 221],
        });
        let leaf4 = Box::new(SimpleNode::Leaf { vals: vec![332] });
        let leaf5 = Box::new(SimpleNode::Leaf {
            vals: vec![4421, 5323],
        });

        let root = Box::new(SimpleNode::Interior {
            vals: vec![(43, leaf1), (100, leaf2), (600, leaf3), (3532, leaf4)],
            left_child: Some(leaf5),
        });
        root
    }

    fn tree_sample_1() -> Box<SimpleNode> {
        let root = Box::new(SimpleNode::Leaf {
            vals: vec![12, 124, 643, 6434],
        });
        root
    }

    #[test]
    fn test_node_split() {
        let root = Box::new(SimpleNode::Leaf {
            vals: vec![12, 521, 800, 1000],
        });
        let (k, l, r) = node_split(root);
        assert_eq!(k, 800);
        assert_eq!(
            *l,
            SimpleNode::Leaf {
                vals: vec![12, 521]
            }
        );
        assert_eq!(
            *r,
            SimpleNode::Leaf {
                vals: vec![800, 1000]
            }
        )
    }

    #[test]
    fn simple_insert_2() {
        let mut root = tree_sample_2();
        println!("{:#?}", root);
        let root = node_insert(root, 123);
        println!("==================================");
        println!("{:#?}", root);

        let root = tree_sample_1();
        println!("{:#?}", root);
        let root = node_insert(root, 1232);
        println!("{:#?}", root);
        panic!()
    }

    #[test]
    fn insert_3() {
        let mut tree = Btree::new();
        tree.insert(12);
        tree.insert(142);
        tree.insert(523);
        tree.insert(1242);
        tree.insert(242);
        tree.insert(123);
        tree.insert(9999);
        tree.insert(7777);
        tree.insert(7778);
        tree.insert(7779);
        println!("{:#?}", tree);
        panic!()
    }

    #[test]
    fn simple_insert_till_overflow() {
        let root = Box::new(SimpleNode::Leaf { vals: Vec::new() });

        let root = match node_insert(root, 1124) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match node_insert(root, 12) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match node_insert(root, 43) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match node_insert(root, 12332) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        assert!(root.contain(12));
        assert!(root.contain(43));
        assert!(!root.contain(44));
        assert!(!root.contain(101));

        println!("{:?}", root);
        panic!()
    }

    #[test]
    fn simple_insert() {
        let root = Box::new(SimpleNode::Leaf { vals: Vec::new() });

        let root = match node_insert(root, 1124) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match node_insert(root, 12) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match node_insert(root, 43) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        assert!(root.contain(12));
        assert!(root.contain(43));
        assert!(!root.contain(44));
        assert!(!root.contain(101));
    }

    #[test]
    fn test_interior_split() {
        let root = tree_sample_2();
        println!("BEFORE SPLIT {:?}", root);
        let (k, l, r) = node_split(root);
        println!("KEY {:?}", k);
        println!("LEFT {:?}", l);
        println!("RIGHT {:?}", r);

        panic!()
    }
}
