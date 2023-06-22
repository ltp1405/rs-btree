#![allow(dead_code)]

trait BtreeNode {
    fn should_split(&self) -> bool;
    fn insert<K: PartialOrd, V>(&mut self, key: &K, val: &V);
}

type Key = u32;
type InteriorVal = (Key, Box<SimpleNode>);

#[derive(Debug, PartialEq)]
pub enum SimpleNode {
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

fn interior_node_insert(mut node: Box<SimpleNode>, val: InteriorVal) -> LeafInsertResult {
    let slot = node.search(val.0);
    let hole = match slot {
        Slot::Hole(h) => h,
        Slot::Cell(c) => panic!(),
    };
    match *node {
        SimpleNode::Interior {
            ref mut vals,
            ref mut left_child,
        } => {
            vals.insert(hole as usize, val);
            if node.overflow() {
                let (k, l, r) = node_split(node);
                return LeafInsertResult::Splitted(k, l, r);
            }
            LeafInsertResult::Normal(node)
        }
        _ => unreachable!(),
    }
}

fn leaf_node_insert(mut node: Box<SimpleNode>, key: u32) -> LeafInsertResult {
    let slot = node.search(key);
    let hole = match slot {
        Slot::Hole(h) => h,
        Slot::Cell(c) => panic!(),
    };
    match *node {
        SimpleNode::Leaf { ref mut vals } => {
            vals.insert(hole as usize, key);
            if node.overflow() {
                let (k, l, r) = node_split(node);
                return LeafInsertResult::Splitted(k, l, r);
            }
            LeafInsertResult::Normal(node)
        }
        _ => unreachable!(),
    }
}

fn node_split(node: Box<SimpleNode>) -> (Key, Box<SimpleNode>, Box<SimpleNode>) {
    match *node {
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
        }
    }

    fn overflow(&self) -> bool {
        let len = match self {
            Self::Interior { vals, left_child } => vals.len(),
            Self::Leaf { vals } => vals.len(),
        };
        len > 3
    }

    fn keys(&self) -> Vec<u32> {
        match self {
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

#[cfg(test)]
mod tests {
    use crate::{leaf_node_insert, node_split, LeafInsertResult};

    use super::SimpleNode;

    fn tree_sample_2() -> Box<SimpleNode> {
        let leaf1 = Box::new(SimpleNode::Leaf { vals: vec![12] });
        let leaf2 = Box::new(SimpleNode::Leaf { vals: vec![98] });
        let leaf3 = Box::new(SimpleNode::Leaf {
            vals: vec![101, 123],
        });
        let leaf4 = Box::new(SimpleNode::Leaf { vals: vec![332] });
        let leaf5 = Box::new(SimpleNode::Leaf {
            vals: vec![4421, 5323],
        });

        let root = Box::new(SimpleNode::Interior {
            vals: vec![(43, leaf1), (100, leaf2), (124, leaf3), (3532, leaf4)],
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
        let root = tree_sample_2();

        let rs = match *root {
            SimpleNode::Leaf { vals } => unreachable!(),
            SimpleNode::Interior { vals, left_child } => {
                vals = {
                    leaf_node_insert(vals[2].1, 12);
                    vals
                }
            }
        };

        println!("{:?}", root);
        panic!()
    }

    #[test]
    fn simple_insert_till_overflow() {
        let root = Box::new(SimpleNode::Leaf { vals: Vec::new() });

        let root = match leaf_node_insert(root, 1124) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match leaf_node_insert(root, 12) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match leaf_node_insert(root, 43) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match leaf_node_insert(root, 12332) {
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

        let root = match leaf_node_insert(root, 1124) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match leaf_node_insert(root, 12) {
            LeafInsertResult::Normal(n) => n,
            LeafInsertResult::Splitted(_, _, _) => unreachable!(),
        };
        let root = match leaf_node_insert(root, 43) {
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
