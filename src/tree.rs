use std::{borrow::Borrow, cell::{RefCell, RefMut}, collections::HashMap, iter::once, marker::PhantomData, mem::size_of, ops::{Bound, DerefMut}, rc::Rc, sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard}};

use byteorder::{BigEndian, ByteOrder,WriteBytesExt};

use self::node::{key_cmp::KeyCmp, node_entry_size_limit, Node, NodeData, OpError};

mod node;

pub use self::node::key_cmp::Lexicological;

type TreeEndian=BigEndian;

const LEAF_FLAG:u16=1;

const NULL_KEY:&[u8]=&[];
const UNDERFLOW_RATIO:f64=0.5;
pub const PAGE_SIZE:usize=4096;

const STUB_BUFFER_LEN:usize=4096;

pub trait PageTable{
    type Guard<'a>:Guard<'a> where Self:'a;
    type MutGuard<'a>:MutGuard<'a> where Self:'a;
    fn get_page(&self,pg_id:u64)->Self::Guard<'_>;
    fn get_page_mut(&self,pg_id:u64)->Self::MutGuard<'_>;
    fn new_page(&self)->(u64,Self::MutGuard<'_>);
    fn remove_page(&self);
}

pub trait Guard<'a>{
    fn get_data(&self)->&[u8];
}
pub trait MutGuard<'a>:Guard<'a>{
    fn get_data_mut(&mut self)->&mut [u8];
}

pub struct Tree<'a,T,KC>
where
    T:PageTable,
    KC:KeyCmp,
{
    root_pg_id:RefCell<u64>,
    page_size:usize,
    page_table:&'a mut T,
    phantom:PhantomData<KC>
}


impl<'a,T,KC> Tree<'a,T,KC>  
where
    T:PageTable,
    KC:KeyCmp,
{
    pub fn new(page_size:usize,table:&mut T)->Tree<T,KC>{
        let (root_pg_id,mut root_guard)=table.new_page();
        let mut root_node:Node<&mut [u8], KC>=Node::new(root_guard.get_data_mut());
        root_node.set_flags(root_node.get_flags()|LEAF_FLAG);
        drop(root_guard);

        Tree::<T,KC>{
            page_table:table,
            page_size,
            phantom:PhantomData,
            root_pg_id:root_pg_id.into(),
        }
        
    }
    
    /// Get the value for key by traversing the tree
    /// and bringing in the pages for nodes along the path.
    pub fn get(&mut self,key:&[u8])->Option<Vec<u8>>{
        let root_pg_id=*self.root_pg_id.borrow();
        let internal=|_:&Self,context:&mut Vec<T::Guard<'_>>,node:&mut Node<&[u8],KC>|{
            context.clear();
            node.upper_bound(Bound::Included(&key)).prev().map(|(_,v)|{TreeEndian::read_u64(v)})
        };
        let leaf=|_:&Self,context:&mut Vec<T::Guard<'_>>,node:&mut Node<&[u8],_>|{
            context.clear();
            node.get(key).map(Vec::from)
        };
        self.search_page(root_pg_id, key, internal, leaf).flatten()
    }

    /// Inserts the key value pair by first finding the 
    /// appropriate leaf node. Tree traversal is same as get
    /// except write guards are acquired instead of read guards
    /// and they are not released until it is guaranteed that the 
    /// corresponding node's child won't split.
    /// 
    /// Currently a node is guaranteed to not split if it has enough
    /// space to insert an entry of max size for the node
    pub fn insert(&mut self,key:&[u8],val:&[u8])->Option<Vec<u8>>{
        //dbg!("Insert",key.len(),val.len());
        assert_ne!(key,NULL_KEY);
        assert!(tree_entry_size_limit(PAGE_SIZE)>=key.len()+val.len());
        let root_pg_id=*self.root_pg_id.borrow();
        let internal=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>,node:&mut Node<&mut [u8],KC>|{
            if node.enough_size(node_entry_size_limit(tree.page_size)){
                context.clear();
            }
            
            node.upper_bound(Bound::Included(&key)).prev().map(|(_,v)|{TreeEndian::read_u64(v)})
        };
        let leaf=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>,node:&mut Node<&mut [u8],_>|{
            if node.enough_size(node_entry_size_limit(tree.page_size)){
                context.clear();
            }
            let (prev,mut push_up)=tree.insert_node(context, node, key, val);
            while push_up.is_some() {
                match context.pop(){
                    // insert into parent node
                    Some(mut guard) => {
                        let (key,val)=push_up.unwrap();
                        let mut val_buf=Vec::new();
                        val_buf.write_u64::<TreeEndian>(val).unwrap();

                        let mut node: Node<&mut [u8], KC>=Node::parse(guard.get_data_mut());
                        let (internal_ptr,internal_push_up)=tree.insert_node(context, &mut node, &key, &val_buf);
                        assert!(internal_ptr.is_none());
                        push_up=internal_push_up;
                    },
                    //New root
                    None => {
                        let (key,val)=push_up.unwrap();
                        let mut new_pg_val_buf=Vec::new();
                        let mut old_root_val_buf=Vec::new();
                        new_pg_val_buf.write_u64::<TreeEndian>(val).unwrap();
                        old_root_val_buf.write_u64::<TreeEndian>(*tree.root_pg_id.borrow()).unwrap();
                        let (new_root_pg_id,mut new_root_guard)=tree.page_table.new_page();
                        
                        let mut node:Node<&mut [u8], KC>=Node::new(new_root_guard.get_data_mut());
                        assert!(node.insert(NULL_KEY,&old_root_val_buf).unwrap().is_none());
                        assert!(node.insert(&key, &new_pg_val_buf).unwrap().is_none());

                        *tree.root_pg_id.borrow_mut()=new_root_pg_id;
                        break;
                    },
                }
            }

            prev
        };
        self.search_page_mut(root_pg_id, key, internal, leaf).flatten()
    }
    
    /// Remove the entry with the key if it exist.
    /// The tree traversal is the same as insert and 
    /// get and write guards are aquired along the path.
    /// Guards are released when its guaranteed that the
    /// child won't merge or redistribute.
    /// 
    /// Currently a node is guaranteed to not merge or redistribute
    /// if after removing the matching entry it is still above the underflow
    /// threshold.
    /// Even if the node underflows, merge or redistribution might not happen
    /// due to variable length entries where redistribution will lead to underflow
    /// of other nodes and merge will lead to overflow.
    pub fn remove(&mut self,key:&[u8])->Option<Vec<u8>>{
        assert_ne!(key,NULL_KEY);
        let root_pg_id=*self.root_pg_id.borrow();
        let internal=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>,node:&mut Node<&mut [u8],KC>|{
            let (interval_key,child_pg_id)= node.upper_bound(Bound::Included(&key)).prev()?;
           
            Some(TreeEndian::read_u64(child_pg_id))
        };
        let leaf=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>,node:&mut Node<&mut [u8],_>|{
            let val=node.remove(key)?;
            
            Some(val)
        };
        self.search_page_mut(root_pg_id, key, internal, leaf).flatten()
    }

    fn insert_node(&self,context:&mut Vec<T::MutGuard<'_>>,node:&mut Node<&mut [u8],KC>,key:&[u8],val:&[u8])->(Option<Vec<u8>>,Option<(Vec<u8>,u64)>){
        if node.enough_size(key.len()+val.len()){
            //dbg!("enough space");
            context.clear();
            match node.insert(key, val){
                Ok(v) => (v,None),
                Err(OpError::EntrySizeExceed) => panic!("Entry size should have been checked already"),
                Err(OpError::InvariantError) => panic!("Invariant Broken"),
                Err(OpError::OutOfSpace) => panic!("Node size should have been checked already"),
            }
        }
        else {
            //dbg!("split");
            let (pg_id,mut new_page)=self.page_table.new_page();
            let mut new_node:Node<&mut [u8], KC>=Node::new(new_page.get_data_mut());
            if Self::is_leaf(node){
                new_node.set_flags(new_node.get_flags()|LEAF_FLAG);
            }
            node.split(&mut new_node);
            
            let (new_node_first_key,_)=new_node.first().expect("Expect split to have at least 1 entry on each node");
            let (old_node_first_key,_)=node.first().expect("Expect split to have at least 1 entry on each node");
            let push_up_key_val=(new_node_first_key.to_owned(),pg_id);
            match key.cmp(new_node_first_key){
                std::cmp::Ordering::Less => {
                    (node.insert(key, val).unwrap(),Some(push_up_key_val))
                },
                std::cmp::Ordering::Greater|std::cmp::Ordering::Equal => {
                    (new_node.insert(key, val).unwrap(),Some(push_up_key_val))
                },
            }
        }
    }


    fn search_page<FInternal,FLeaf,R>(&self,node_pg_id:u64,key:&[u8],mut internal:FInternal,mut leaf:FLeaf)->Option<R>
    where
        FInternal:FnMut(&Self,&mut Vec<T::Guard<'_>>,&mut Node<&[u8],KC>)->Option<u64>,
        FLeaf:FnMut(&Self,&mut Vec<T::Guard<'_>>,&mut Node<&[u8],KC>)->R
    {
        let mut context=Vec::new();
        let mut cur_pg_id=node_pg_id;
        let result=loop {
            let pg_guard=self.page_table.get_page(cur_pg_id);
            let mut node:Node<&[u8],KC>=Node::parse(pg_guard.get_data());
            if Self::is_leaf(&node){
                break Some(leaf(self,&mut context,&mut node));
            }
            else{
                match internal(self,&mut context,&mut node){
                    Some(pg_id) => {
                        cur_pg_id=pg_id;
                        context.push(pg_guard);
                    },
                    None => break None,
                }
            }
        };

        result
    }


    fn search_page_mut<FInternal,FLeaf,R>(&mut self,node_pg_id:u64,key:&[u8],mut internal:FInternal,mut leaf:FLeaf)->Option<R>
    where
        FInternal:FnMut(&Self,&mut Vec<T::MutGuard<'_>>,&mut Node<&mut [u8],KC>)->Option<u64>,
        FLeaf:FnMut(&Self,&mut Vec<T::MutGuard<'_>>,&mut Node<&mut [u8],KC>)->R,
    {
        let mut context=Vec::new();
        let mut cur_pg_id=node_pg_id;
        let result=loop {
            let mut pg_guard=self.page_table.get_page_mut(cur_pg_id);
            let mut node:Node<&mut [u8],KC>=Node::parse(pg_guard.get_data_mut());
            if Self::is_leaf(&node){
                break Some(leaf(self,&mut context,&mut node));
            }
            else{
                match internal(self,&mut context,&mut node){
                    Some(pg_id) => {
                        cur_pg_id=pg_id;
                        context.push(pg_guard);
                    },
                    None => break None,
                }
            }
        };

        result
    }

    fn is_leaf<S:NodeData>(node:&Node<S,KC>)->bool{
        (node.get_flags()&LEAF_FLAG)!=0
    }
}

/// Get the max number of bytes an entry can have
/// for insertion into the tree given the node size
/// This value will be smaller than node size limit
/// since internal node can potentially be larger than lead node.
fn tree_entry_size_limit(size:usize)->usize{
    node_entry_size_limit(size)-size_of::<u64>()
}

#[derive(Default)]
pub struct StubPageTable{
    buffer_pool:Vec<RwLock<Vec<u8>>>,
    pg_id_counter:RefCell<u64>,
}

impl StubPageTable {
    pub fn new()->StubPageTable{
        let pool:Vec<RwLock<Vec<u8>>>=(0..STUB_BUFFER_LEN).map(|_|RwLock::new(vec![0;PAGE_SIZE])).collect();
        StubPageTable{
            buffer_pool:pool,
            pg_id_counter:RefCell::new(0)
        }
    }
    pub fn reset(&self){
        *self.pg_id_counter.borrow_mut()=0;
    }
}


impl PageTable for StubPageTable{
    type Guard<'b>=RwLockReadGuard<'b,Vec<u8>> where Self: 'b;

    type MutGuard<'b>=RwLockWriteGuard<'b,Vec<u8>> where Self: 'b;

    fn get_page(&self,pg_id:u64)->Self::Guard<'_> {
        self.buffer_pool.get(pg_id as usize).unwrap().read().unwrap()
    }

    fn get_page_mut(&self,pg_id:u64)->Self::MutGuard<'_> {
        self.buffer_pool.get(pg_id as usize).unwrap().write().unwrap()
    }
    
    fn new_page(&self)->(u64,Self::MutGuard<'_>) {
        let new_pg_id=*self.pg_id_counter.borrow_mut();
        assert!((new_pg_id as usize) < self.buffer_pool.len(),"Stub only have {} pages",self.buffer_pool.len());
        *self.pg_id_counter.borrow_mut()+=1;

        let lock_ref=&(*self.buffer_pool)[new_pg_id as usize];
        
        (new_pg_id,lock_ref.write().unwrap())
    }
    
    fn remove_page(&self) {
        
    }
}

impl Guard<'_> for RwLockReadGuard<'_,Vec<u8>> {
    fn get_data(&self)->&[u8] {
        self.as_slice()
    }
}

impl Guard<'_> for RwLockWriteGuard<'_,Vec<u8>> {
    fn get_data(&self)->&[u8] {
        self.as_slice()
    }
}

impl MutGuard<'_> for RwLockWriteGuard<'_,Vec<u8>> {
    fn get_data_mut(&mut self)->&mut [u8] {
        self.as_mut_slice()
    }
}

#[cfg(test)]
mod test{
    use std::collections::BTreeMap;

    use proptest::proptest;

    use crate::{tree::PAGE_SIZE, utils::{generate_kv_strategy, generate_string}};

    use super::{node::key_cmp::Lexicological, StubPageTable, Tree};
    use rand::prelude::*;

    #[test]
    fn basic(){
        let mut btree=BTreeMap::new();
        let mut stub=StubPageTable::new();
        let mut my_tree:Tree<StubPageTable, Lexicological>=Tree::new(PAGE_SIZE,&mut stub);
        let mut inputs:Vec<(String,String)>=(100..400).map(|_|(generate_string(5..100),generate_string(5..100))).collect();

        let mut entry_size_acc=0;
        for (i,(k,v)) in inputs.iter().cloned().enumerate(){
            entry_size_acc+=k.len()+v.len();
            assert_eq!(my_tree.insert(k.as_bytes(), v.as_bytes()),btree.insert(k, v).map(Vec::from));
        }
        
        inputs.shuffle(&mut thread_rng());

        for (k,v) in &inputs{
            assert_eq!((btree.get(k).map(|v|(*v).clone())).map(Vec::from),my_tree.get(k.as_bytes()));
        }

    }

    proptest!{
        #[test]
        fn prop_tree((input,get,remove,range) in generate_kv_strategy(200,500)){
            let mut btree=BTreeMap::new();
            let mut stub=StubPageTable::new();
            let mut my_tree=Tree::new(PAGE_SIZE,&mut stub);
            prop_insert(&mut my_tree, &mut btree, input.iter().map(|(k,v)|{(k.as_ref(),v.as_ref())}).collect());
            prop_get(&mut my_tree, &mut btree, get.iter().map(|i|{input[*i].0.as_ref()}).collect());
            prop_remove(&mut my_tree, &mut btree, remove.iter().map(|i|{input[*i].0.as_ref()}).collect());
            prop_get(&mut my_tree, &mut btree, get.iter().map(|i|{input[*i].0.as_ref()}).collect());
        }
    }

    
    fn prop_insert(tree:&mut Tree<'_,StubPageTable,Lexicological>,btree:&mut BTreeMap<String,String>,input:Vec<(&str,&str)>){
        for (k,v) in input{
            assert_eq!(tree.insert(k.as_bytes(), v.as_bytes()),btree.insert(k.to_owned(), v.to_owned()).map(Vec::from));
        }
    }

    fn prop_get(tree:&mut Tree<'_,StubPageTable,Lexicological>,btree:&mut BTreeMap<String,String>,input:Vec<&str>){
        for k in input{
            assert_eq!(tree.get(k.as_bytes()),btree.get(k).map(|v|Vec::from(v.to_owned())));
        }
    }

    fn prop_remove(tree:&mut Tree<'_,StubPageTable,Lexicological>,btree:&mut BTreeMap<String,String>,input:Vec<&str>){
        for k in input{
            assert_eq!(tree.remove(k.as_bytes()),btree.remove(k).map(|v|Vec::from(v.to_owned())));
        }
    }

}