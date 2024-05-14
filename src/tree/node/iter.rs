use super::{key_cmp::KeyCmp, Node};


pub struct EntryRefIter<'a,T>
where
    T:KeyCmp
{
    idx:usize,
    node:&'a Node<'a,T>
}


impl<'a,T> Iterator for EntryRefIter<'a,T> 
where
    T:KeyCmp
{
    type Item=(&'a[u8],&'a[u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if (self.idx) < self.node.len(){
            let res=Some((self.node.get_key_slice_at(self.idx),self.node.get_val_slice_at(self.idx)));
            self.idx+=1;
            res
        }
        else{
            None
        }
    }
    
}

impl<'a,T> EntryRefIter<'a,T> 
where
    T:KeyCmp
{
    pub fn new(node:&'a Node<'a,T>)->EntryRefIter<'a,T>{
        EntryRefIter{
            idx:0,
            node
        }
    }
}