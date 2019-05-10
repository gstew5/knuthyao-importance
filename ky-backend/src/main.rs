extern crate rand;
use rand::prelude::*;
use std::time::{Instant};

#[derive(Debug,Clone,Copy,PartialEq)]
enum Event {
    A,
    B,
}

enum Tree<A> {
    Leaf(A),
    Node(Box<Tree<A>>, Box<Tree<A>>),
    Hole
}

use Tree::*;

type Index = u16;
const NUM_BITS: usize = 16;
const NUM_ENTRIES: usize = 1<<NUM_BITS;

fn event_of<A: Clone>(t: &Tree<A>, i: Index) -> Option<A> {
    match t {
        Leaf(a) => Some(a.clone()),
        Node(t1, t2) =>
            if i % 2 == 0 {
                event_of(&*t1, i>>1)
            } else {
                event_of(&*t2, i>>1)
            },
        Hole => None
    }
}

fn materialize<A: Clone>(t: &Tree<A>, entries: &mut [Option<A>]) -> () {
    for i in 0..NUM_ENTRIES {
        entries[i] = event_of(t, i as u16)
    }
}

fn main() {
    let tree: Tree<Event> =
        Node(Box::new(Leaf(Event::A)),
             Box::new(Node(Box::new(Leaf(Event::B)),
                           Box::new(Hole))));
    let mut entries: [Option<Event>; NUM_ENTRIES] = [None; NUM_ENTRIES];
    materialize(&tree, &mut entries[..]);

    let mut num_as = 0;
    let mut num_bs = 0;
    let mut num_nones = 0;
    let mut rng = thread_rng();
    let now = Instant::now();    
    for _ in 0..10_000_000 {
        let i: Index = rng.gen();
        match entries[i as usize] {
            Some(Event::A) => num_as += 1,
            Some(Event::B) => num_bs += 1,
            None => num_nones += 1,
        }
    };
    let elapsed = now.elapsed();    
    println!("As = {}, Bs = {}, Nones = {}", num_as, num_bs, num_nones);
    println!("time = {}s, {}ms", elapsed.as_secs(), elapsed.subsec_millis())    
}

