use hashbrown::hash_map::HashMap;

mod lut;
use self::lut::*;

#[derive(Debug,Clone)]
enum Event {
    A,
    B,
    C
}

fn main() {
    let mut lut: HashMap<u8, (u8, Event)> = PLUT::new();

    lut.ins(3, 8, Event::A).expect("error");
    lut.ins(1<<7, 2, Event::B).expect("error");
    lut.ins(3<<6, 2, Event::C).expect("error");    

    println!("lut = {:?}", lut);
    
    let v = lut.par_get(3<<6 | 1).expect("error");
    println!("v = {:?}", v);
}
