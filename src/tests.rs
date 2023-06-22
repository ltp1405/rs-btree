use std::collections::BTreeMap;

use crate::{Btree, InsertResult};

use super::SimpleNode;

#[test]
fn random_insert() {
    use rand::Rng;

    let mut rng = rand::thread_rng();
    let mut values: Vec<i64> = Vec::new();
    for _ in 0..10000000 {
        values.push(rng.gen());
    }

    let mut tree = Btree::new();

    for v in values.clone() {
        tree.insert(v, ());
    }

    // for v in values.clone() {
    //     tree.get(&v).unwrap();
    // }
    panic!()
}

#[test]
fn insert() {
    let mut tree = Btree::new();
    tree.insert(12, ());
    tree.insert(142, ());
    tree.insert(523, ());
    tree.insert(1242, ());
    tree.insert(242, ());
    tree.insert(123, ());
    tree.insert(9999, ());
    tree.insert(7777, ());
    tree.insert(7778, ());
    tree.insert(7779, ());

    println!("{:#?}", tree);
    tree.get(&12).unwrap();
    tree.get(&142).unwrap();
    tree.get(&523).unwrap();
    tree.get(&7777).unwrap();
    tree.get(&9999).unwrap();
    tree.get(&7778).unwrap();
}
