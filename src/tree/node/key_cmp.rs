use std::cmp::Ordering;


pub trait KeyCmp{
    fn cmp(key1:&[u8],key2:&[u8])->Ordering;
}

pub enum Lexicological {}

impl KeyCmp for Lexicological {
    fn cmp(key1:&[u8],key2:&[u8])->Ordering {
        key1.cmp(key2)
    }
}