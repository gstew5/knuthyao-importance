extern crate sexp;
use sexp::{Sexp,Atom};

extern crate rand;
use rand::prelude::*;

#[derive(Debug,Clone,Copy,PartialEq)]
pub enum Event {
    A,
    B,
}

#[derive(Debug,Clone)]
pub enum Tree<A> {
    Leaf(A),
    Node(Box<Tree<A>>, Box<Tree<A>>),
    Hole
}

use self::Tree::*;

trait FromSexp {
    fn from_sexp(e: &sexp::Sexp) -> Option<Self> where Self: std::marker::Sized;
}

impl FromSexp for Tree<String> {
    fn from_sexp(e: &Sexp) -> Option<Self> {
        match e {
            Sexp::Atom(a) => {
                match a { 
                    Atom::S(s) => {
                        if s.is_empty() {
                            Some(Hole)
                        } else {
                            Some(Leaf(s.clone()))
                        }
                    },
                    Atom::I(_) => None,
                    Atom::F(_) => None
                }
            },
            Sexp::List(v) => {
                if v.len() == 2 {
                    let t1 = Self::from_sexp(&v[0])?;
                    let t2 = Self::from_sexp(&v[1])?;
                    Some(Node(Box::new(t1), Box::new(t2)))
                } else {
                    None
                }
            }
        }
    }
}

pub fn parse_str(s: &str) -> Result<Tree<String>, &'static str> {
    match sexp::parse(s) {
        Ok(e) => {
            match Tree::from_sexp(&e) {
                Some(t) => Ok(t),
                None => Err("failure: sexp->tree")
            }
        },
        Err(_) => Err("failure: string->sexp")
    }
}

pub type Index = u8;
pub const NUM_BITS: usize = 8;
pub const NUM_ENTRIES: usize = 1<<NUM_BITS;

fn subtree_of_aux<'a, A: Clone>
    (n: usize, root: &'a Tree<A>, t: &'a Tree<A>, i: Index) -> &'a Tree<A> {
    if n == 0 {
        &Hole
    } else {
        match t {
            Leaf(_) => &t,
            Node(t1, t2) =>
                if i % 2 == 0 {
                    subtree_of_aux(n-1, root, t1, i>>1)
                } else {
                    subtree_of_aux(n-1, root, t2, i>>1)
                },
            Hole => subtree_of_aux(n, root, root, i)
        }
    }
}

fn subtree_of<A: Clone>(t: &Tree<A>, i: Index) -> &Tree<A> {
    subtree_of_aux(NUM_BITS, t, t, i)
}

pub fn event_of<A: Clone>(root: &Tree<A>, t: &Tree<A>) -> A {
    match t {
        Leaf(a) => a.clone(),
        Node(t1, t2) => {
            let mut rng = thread_rng();
            if rng.gen() {
                event_of(root, t1)
            } else {
                event_of(root, t2)
            }
        },
        Hole => event_of(root, root)
    }
}

pub fn materialize<'a, A: Clone>(t: &'a Tree<A>, entries: &mut [&'a Tree<A>]) -> () {
    for i in 0..NUM_ENTRIES {
        entries[i] = subtree_of(t, i as u8)
    }
}

#[test]
fn repeated_inference() {
    let tree: Tree<Event> =
        Node(Box::new(Leaf(Event::A)),
             Box::new(Node(Box::new(Leaf(Event::B)),
                           Box::new(Hole))));
    let mut entries: [&Tree<Event>; NUM_ENTRIES] = [&Hole; NUM_ENTRIES];
    materialize(&tree, &mut entries[..]);

    let num_trials = 10_000_000;
    let mut num_as = 0;
    let mut num_bs = 0;

    let mut rng = thread_rng();
    for _ in 0..num_trials {
        let i: Index = rng.gen();
        let t: &Tree<Event> = entries[i as usize];
        match event_of(&tree, t) {
            Event::A => num_as += 1,
            Event::B => num_bs += 1
        }
    };
    let result = num_as as f64/(num_as + num_bs) as f64;
    assert!(0.66-0.05 <= result && result <= 0.66+0.05);
}

