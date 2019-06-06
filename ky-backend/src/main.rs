extern crate rand;
use rand::prelude::*;

use std::fs;
use std::env;
use std::collections::HashMap;

mod lib;
use lib::*;

fn help() {
    println!("usage: cargo run [--release] file num_trials")
}

fn main() {
    let args: Vec<String> = env::args().collect();
    if args.len() != 3 {
        help();
        panic!("wrong number of arguments")
    }
    let file = args[1].clone();
    let num_trials: u64 = args[2].parse().expect("num_trials must be an integer");    
    let s = fs::read_to_string(&file).expect(&format!("main: couldn't read {}", file));
    let tree = parse_str(&s[..]).expect("parse failure");
    let mut entries: [&Tree<String>; NUM_ENTRIES] = [&Tree::Hole; NUM_ENTRIES];
    materialize(&tree, &mut entries[..]);
    let mut counts: HashMap<String, u64> = HashMap::new();
    let mut rng = thread_rng();    
    for _ in 0..num_trials {
        let i: Index = rng.gen();
        let t: &Tree<String> = entries[i as usize];
        let k = event_of(&tree, t);
        match counts.get(&k) {
            Some(c) => counts.insert(k, c+1),
            None => counts.insert(k, 0)
        };
    };
    println!("{:?}", counts)
}
