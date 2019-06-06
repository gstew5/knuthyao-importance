extern crate rand;
use rand::prelude::*;

#[macro_use]
extern crate criterion;

use criterion::Criterion;
use criterion::black_box;

#[path="../src/lib.rs"]
mod lib;
use lib::*;
use Tree::*;

fn materialize_bench(c: &mut Criterion) {
    let tree: Tree<Event> =
        Node(Box::new(Leaf(Event::A)),
             Box::new(Node(Box::new(Leaf(Event::B)),
                           Box::new(Hole))));
    let mut entries: [&Tree<Event>; NUM_ENTRIES] = [&Hole; NUM_ENTRIES];
    c.bench_function("materialize2-3,1-3",
                     |b| b.iter(|| materialize(black_box(&tree), &mut entries[..])));
}

fn infer_one(tree: &Tree<Event>, entries: &[&Tree<Event>]) {
    let mut rng = thread_rng();
    let i: Index = rng.gen();
    let t: &Tree<Event> = entries[i as usize];
    match event_of(&tree, t) {
        Event::A => (),
        Event::B => ()
    }
}

fn infer_bench(c: &mut Criterion) {
    let tree: Tree<Event> =
        Node(Box::new(Leaf(Event::A)),
             Box::new(Node(Box::new(Leaf(Event::B)),
                           Box::new(Hole))));
    let mut entries: [&Tree<Event>; NUM_ENTRIES] = [&Hole; NUM_ENTRIES];    
    materialize(&tree, &mut entries[..]);
    c.bench_function("infer2-3,1-3", |b| b.iter(|| infer_one(black_box(&tree), &entries)));
}

criterion_group!(benches, materialize_bench, infer_bench);
criterion_main!(benches);



