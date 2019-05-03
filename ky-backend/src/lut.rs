use hashbrown::hash_map::HashMap;

//A map from u8's to V's, to be implemented (eventually) on
//ternary CAMs. It's a "PLUT" rather than a "LUT" because
//inserted keys can be partial, as in:
//  (0010 XXXX, Event A)
//where "X" stands for "don't care".
//INVARIANTS:
//~~~~~~~~~~~
// 1. Unlike in a general TCAM, X bits appear only at the end of keys,
//    not at arbitrary positions. 
// 2. We enforce (in ins) that no two distinct values are associated with
//    common-prefix keys, which makes lookups deterministic.
pub trait PLUT<V> {
    fn new() -> Self;
    //Look up key k in SIMD parallel.
    //Returns (optionally) the number of bits consumed together
    //with the associated value.
    fn par_get(&self, k: u8) -> Option<&(u8, V)>;
    //Insert key-value pair (k,v), where size is the number of
    //bits we care about in k, counting from MSB.
    fn ins(&mut self, k: u8, size: u8, v: V) -> Result<(), String>;
}

const KEY_BITS: u8 = 8;
const MAX_U8: u8 = 255;

impl<V: Clone> PLUT<V> for HashMap<u8, (u8, V)> {
    fn new() -> Self {
        HashMap::new()
    }

    fn par_get(&self, k: u8) -> Option<&(u8, V)> {
        HashMap::get(self, &k)
    }

    fn ins(&mut self, k: u8, size: u8, v: V) -> Result<(), String> {
        if let Some(_) = HashMap::get(self, &k) {
            Err(format!("key {} is already bound", k))
        } else if size > KEY_BITS {
            Err(format!("size {} is greater then key size {}", size, KEY_BITS))
        } else {
            let xbits = KEY_BITS - size;
            for i in 0..(1<<xbits) {
                let key = (k & (MAX_U8<<xbits)) | i;
                HashMap::insert(self, key, (size, v.clone()));
            };
            Ok(())
        }
    }
}
