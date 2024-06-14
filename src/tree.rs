use std::{any::TypeId, borrow::Borrow, cell::{RefCell, RefMut}, collections::HashMap, iter::once, marker::PhantomData, mem::size_of, ops::{Bound, DerefMut, RangeBounds}, rc::Rc, sync::{Mutex, MutexGuard, RwLock, RwLockReadGuard, RwLockWriteGuard}};

use byteorder::{BigEndian, ByteOrder,WriteBytesExt, LE};
use node::MutNodeData;
use proptest::num::f32::NORMAL;

use self::node::{key_cmp::KeyCmp, node_entry_size_limit, Node, NodeData, OpError};

mod node;

pub use self::node::key_cmp::Lexicological;

type TreeEndian=BigEndian;

const LEAF_FLAG:u16=1;
const LEFT_PTR_FLAG:u16=2;
const RIGHT_PTR_FLAG:u16=4;
const LOWER_PTR_FLAG:u16=LEFT_PTR_FLAG;

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
    KC:KeyCmp+'static,
{
    root_pg_id:RefCell<u64>,
    page_size:usize,
    page_table:&'a T,
    phantom:PhantomData<KC>
}


impl<'a,T,KC> Tree<'a,T,KC>  
where
    T:PageTable,
    KC:KeyCmp,
{
    pub fn new(page_size:usize,table:&T)->Tree<T,KC>{
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
        let guard=self.get_leaf(key)?;
        let node: Node<&[u8], KC>=Node::parse(guard.get_data());
        node.get(key).map(Vec::from)
    }

    /// Get the guard for the leaf node where the input key
    /// belongs to the node's key space. Traversal is same as get
    pub fn get_leaf(&self,key:&[u8])->Option<T::Guard<'a>>{
        let root_pg_id=*self.root_pg_id.borrow();
        let internal=|_:&Self,context:&mut Vec<T::Guard<'_>>|{
            let cur_guard=context.pop().unwrap();
            let node: Node<&[u8], KC>=Node::parse(cur_guard.get_data());
            context.clear();

            let child_ptr=get_child_or_low_ptr(&node, key);
            
            context.push(cur_guard);
            child_ptr
        };
        let leaf=|_:&Self,context:&mut Vec<T::Guard<'a>>|{
            let cur_guard=context.pop().unwrap();
            context.clear();
            
            cur_guard
        };
        self.search_page(root_pg_id, key, internal, leaf)
    }

    pub fn for_range<'b,R,F>(&self,range:R,mut f:F)
    where
        R: RangeBounds<&'b [u8]>+Clone,
        F:FnMut((&[u8],&[u8]))
    {
        // For now assume its lexicological
        assert!(TypeId::of::<KC>()==TypeId::of::<Lexicological>());
        let start_key=match range.start_bound(){
            Bound::Included(k) | Bound::Excluded(k) => {
                k
            },
            Bound::Unbounded => {
                [].as_slice()
            },
        };
        
        let mut leaf_guard=self.get_leaf(start_key);
        while let Some(guard)=leaf_guard{
            let node: Node<&[u8], KC>=Node::parse(guard.get_data());
            assert!(is_leaf(&node));
            if node.len()==0{
                leaf_guard=get_right_sibling_ptr(&node).map(|ptr|self.page_table.get_page(ptr));
                continue;
            }
            node
            .range(range.clone())
            .for_each(&mut f);
            match range.end_bound(){
                Bound::Included(k) | Bound::Excluded(k) => {
                    if node.last().unwrap().0>=k{
                        return;
                    }
                },
                Bound::Unbounded => {},
            }
            leaf_guard=get_right_sibling_ptr(&node).map(|ptr|self.page_table.get_page(ptr));
        }
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
        let internal=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>|{
            let mut pg_guard=context.pop().unwrap();
            let node: Node<&mut [u8], KC>=Node::parse(pg_guard.get_data_mut());
            if node.enough_size(node_entry_size_limit(tree.page_size)){
                context.clear();
            }
            let child_ptr=get_child_or_low_ptr(&node, key);

            context.push(pg_guard);
            child_ptr
        };
        let leaf=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>|{
            let mut pg_guard=context.pop().unwrap();
            let mut node=Node::parse(pg_guard.get_data_mut());
            if node.enough_size(node_entry_size_limit(tree.page_size)){
                context.clear();
            }

            let (prev,mut push_up)=tree.insert_node(context, &mut node, key, val);
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
                        new_pg_val_buf.write_u64::<TreeEndian>(val).unwrap();
                        let (new_root_pg_id,mut new_root_guard)=tree.page_table.new_page();
                        
                        let mut node:Node<&mut [u8], KC>=Node::new(new_root_guard.get_data_mut());
                        node.set_ptrs(*tree.root_pg_id.borrow(), 0);
                        node.set_flags(node.get_flags()|LOWER_PTR_FLAG);
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
    /// Guards are released when its guaranteed that its
    /// child won't be removed
    /// 
    /// Currently a node is guaranteed to be removed if it has
    /// at least 2 or more entries
    pub fn remove(&mut self,key:&[u8])->Option<Vec<u8>>{
        assert_ne!(key,NULL_KEY);
        let root_pg_id=*self.root_pg_id.borrow();
        let internal=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>|{
            let mut pg_guard=context.pop().unwrap();
            let node: Node<&mut [u8], KC>=Node::parse(pg_guard.get_data_mut());
            if node.len()+(node.get_flags()&LOWER_PTR_FLAG).min(1) as usize>1{
                context.clear()
            }
            let child_ptr=get_child_or_low_ptr(&node, key);
            
            context.push(pg_guard);
            child_ptr
        };
        let leaf=|tree:&Self,context:&mut Vec<T::MutGuard<'_>>|{
            let mut pg_guard=context.pop().unwrap();
            let mut node: Node<&mut [u8], KC>=Node::parse(pg_guard.get_data_mut());

            assert!(node.get_flags()&LOWER_PTR_FLAG==0);
            let val=node.remove(key);
            if node.len()>0{
                context.clear();
                return val;
            }
            
            // At this point the leaf node is know to be empty and 
            // the entire chain(maybe just the leaf) needs to be removed

            // Recursive remove internal nodes
            // The first guard in context is the first node with more than 1 child
            
            // Just leave leaf empty for now
            // while let Some(mut parent_guard)=context.pop() {
            //     let mut parent: Node<&mut [u8], KC>=Node::parse(parent_guard.get_data_mut());

            //     remove_child(&mut parent, key);

            //     // If after removal the node is not empty it means the node was safe
            //     // and there should be no parent guards
            //     if parent.len()+(parent.get_flags()&LOWER_PTR_FLAG).min(1) as usize>0{
            //         assert!(context.is_empty());
            //     }
            
            // }

            val
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

            node.split(&mut new_node);

            if is_leaf(node){
                new_node.set_flags(new_node.get_flags()|LEAF_FLAG);

                if let Some(righ_ptr) = get_right_sibling_ptr(node) {
                    new_node.set_flags(new_node.get_flags()|RIGHT_PTR_FLAG);
                    new_node.set_ptrs(0, righ_ptr);
                }
                node.set_flags(node.get_flags()|RIGHT_PTR_FLAG);
                node.set_ptrs(0, pg_id);
            }
            
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
        FInternal:FnMut(&Self,&mut Vec<T::Guard<'a>>)->Option<u64>,
        FLeaf:FnMut(&Self,&mut Vec<T::Guard<'a>>)->R,
        R:'a
    {
        let mut context=Vec::new();
        let mut cur_pg_id=node_pg_id;
        let result=loop {
            let pg_guard=self.page_table.get_page(cur_pg_id);
            let mut node:Node<&[u8],KC>=Node::parse(pg_guard.get_data());
            if is_leaf(&node){
                context.push(pg_guard);
                break Some(leaf(self,&mut context));
            }
            else{
                context.push(pg_guard);
                match internal(self,&mut context){
                    Some(pg_id) => {
                        cur_pg_id=pg_id;
                    },
                    None => break None,
                }
            }
        };

        result
    }

    fn search_page_mut<FInternal,FLeaf,R>(&mut self,node_pg_id:u64,key:&[u8],mut internal:FInternal,mut leaf:FLeaf)->Option<R>
    where
        FInternal:FnMut(&Self,&mut Vec<T::MutGuard<'a>>)->Option<u64>,
        FLeaf:FnMut(&Self,&mut Vec<T::MutGuard<'a>>)->R,
        R:'a
    {
        let mut context=Vec::new();
        let mut cur_pg_id=node_pg_id;
        let result=loop {
            let mut pg_guard=self.page_table.get_page_mut(cur_pg_id);
            let mut node:Node<&mut [u8],KC>=Node::parse(pg_guard.get_data_mut());
            if is_leaf(&node){
                context.push(pg_guard);
                break Some(leaf(self,&mut context));
            }
            else{
                context.push(pg_guard);
                match internal(self,&mut context){
                    Some(pg_id) => {
                        cur_pg_id=pg_id;
                    },
                    None => break None,
                }
            }
        };

        result
    }

    /// help debugging by cloning all entries within
    /// the range into vectors.
    fn collect_entries<'b,R>(&self,r:R)->Vec<(Vec<u8>,Vec<u8>)>
    where
        R:RangeBounds<&'b [u8]> + Clone
    {
        let mut my_tree_entries=Vec::new();
        self.for_range(r, |(k,v)|{
            my_tree_entries.push((k.to_vec(),v.to_vec()));
        });

        my_tree_entries
    }
}

fn remove_child<S,KC>(node:&mut Node<S,KC>,key:&[u8])->u64
where
    S:MutNodeData,
    KC:KeyCmp
{
    match node.upper_bound(Bound::Included(&key)).prev(){
        // Remove key pointing to empty child
        Some((k,v)) => {
            let key=k.to_owned();
            node.remove(&key).map(|v|TreeEndian::read_u64(&v)).unwrap()
        },
        // Remove lower pointer to empty child
        None => {
            let low_ptr=get_low_ptr(node).unwrap();
            match node.first(){
                // Move first entry's pid into lower pointer
                Some((k,v)) => {
                    let k=k.to_owned();
                    let new_low=TreeEndian::read_u64(v);
                    node.remove(&k);
                    node.set_ptrs(new_low, 0);
                },
                // Just toggle lower pointer
                None => {
                    node.set_flags(node.get_flags()&!LOWER_PTR_FLAG);
                },
            };
            low_ptr
        },
    }
    
}

fn get_child_or_low_ptr<S,KC>(node:&Node<S,KC>,key:&[u8])->Option<u64>
where
    S:NodeData,
    KC:KeyCmp
{
    node
    .upper_bound(Bound::Included(&key))
    .prev()
    .map(|(_,v)|{TreeEndian::read_u64(v)})
    .or(get_low_ptr(node))
}

fn get_low_ptr<S,KC>(node:&Node<S,KC>)->Option<u64>
where
    S:NodeData,
    KC:KeyCmp
{
    assert!(!is_leaf(node));
    if node.get_flags()&LOWER_PTR_FLAG!=0{
        Some(node.get_ptrs().0)
    }
    else {
        None
    }
}

fn get_left_sibling_ptr<S,KC>(node:&Node<S,KC>)->Option<u64>
where
    S:NodeData,
    KC:KeyCmp
{
    assert!(is_leaf(node));
    if node.get_flags()&LEFT_PTR_FLAG!=0{
        Some(node.get_ptrs().0)
    }
    else {
        None
    }
}

fn get_right_sibling_ptr<S,KC>(node:&Node<S,KC>)->Option<u64>
where
    S:NodeData,
    KC:KeyCmp
{
    assert!(is_leaf(node));
    if node.get_flags()&RIGHT_PTR_FLAG!=0{
        Some(node.get_ptrs().1)
    }
    else {
        None
    }
}

/// Check if node is leaf node
fn is_leaf<S,KC>(node:&Node<S,KC>)->bool
where
    S:NodeData,
    KC:KeyCmp
{
    (node.get_flags()&LEAF_FLAG)!=0
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
    use core::panic;
    use std::{borrow::Borrow, collections::BTreeMap, io::stdin, thread::panicking};

    use proptest::{prelude::prop, proptest};

    use crate::{tree::{get_right_sibling_ptr, is_leaf, PAGE_SIZE}, utils::{generate_kv_strategy, generate_string}};

    use super::{ node::{key_cmp::Lexicological, Node}, Guard, PageTable, StubPageTable, Tree};
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
        my_tree.get(&[]);
        
        inputs.shuffle(&mut thread_rng());

        for (k,v) in &inputs{
            assert_eq!((btree.get(k).map(|v|(*v).clone())).map(Vec::from),my_tree.get(k.as_bytes()));
        }

        let my_tree_entries=my_tree.collect_entries(..);
        if !btree.iter().map(|(k,v)|(k.as_bytes(),v.as_bytes())).eq(my_tree_entries.iter().map(|(k,v)|(k.borrow(),v.borrow()))){
            panic!("all entry scan is different");
        }

    }

    proptest!{
        #[test]
        fn prop_tree((input,get,remove,range) in generate_kv_strategy(200,500)){
            let mut btree=BTreeMap::new();
            let mut stub=StubPageTable::new();
            let mut my_tree=Tree::new(PAGE_SIZE,&stub);
            prop_insert(&mut my_tree, &mut btree, input.iter().map(|(k,v)|{(k.as_ref(),v.as_ref())}).collect());
            prop_get(&mut my_tree, &mut btree, get.iter().map(|i|{input[*i].0.as_ref()}).collect());
            prop_remove(&mut my_tree, &mut btree, remove.iter().map(|i|{input[*i].0.as_ref()}).collect());
            prop_get(&mut my_tree, &mut btree, get.iter().map(|i|{input[*i].0.as_ref()}).collect());
            prop_range(&stub,&mut my_tree, &mut btree, range.iter().map(|(k,v)|(k,v)).collect());
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
            assert_eq!(tree.get(k.as_bytes()),btree.get(k).map(|v|Vec::from(v.to_owned())));
        }
    }

    fn prop_range(table:&StubPageTable,tree:&mut Tree<'_,StubPageTable,Lexicological>,btree:&mut BTreeMap<String,String>,input:Vec<(&String,&String)>){
        for (start,end) in input{
            let my_tree_entries: Vec<(Vec<u8>, Vec<u8>)>=tree.collect_entries(start.as_bytes()..end.as_bytes());
            if !btree.range::<String,_>(start..end).map(|(k,v)|(k.as_bytes(),v.as_bytes())).eq(my_tree_entries.iter().map(|(k,v)|(k.borrow(),v.borrow()))){
                panic!("Different entries. std_count: {} my_count: {}",btree.range::<String,_>(start..end).count(),my_tree_entries.len());
            }
            

            // while let Some(guard)=leaf_guard{
            //     let mut node: Node<&[u8], Lexicological>=Node::parse(guard.get_data());
            //     if node.len()==0{
            //         leaf_guard=get_right_sibling_ptr(&node).map(|ptr|table.get_page(ptr));
            //         continue;
            //     }

            //     let std_iter_ref=std_iter
            //     .by_ref()
            //     .map(|(k,v)|{
            //         (k.as_bytes(),v.as_bytes())
            //     });
            //     assert!(is_leaf(&node));
            //     assert!(node.len()>0);

            //     let mut node_iter=node
            //     .range(start.as_bytes()..end.as_bytes())
            //     .inspect(|(k,_)|{
            //         assert!(last_key.as_slice()<k);
            //         last_key=k.to_vec();
            //     });
                
            //     for (k,v) in std_iter_ref{
            //         let node_kv=node_iter.next().unwrap();
            //         if (k,v)!=node_kv{
            //             panic!("{match_count} {:?} {:?}",(k,v),node_kv);
            //         }
            //         match_count+=1;
            //     }

            //     assert!(node_iter.next().is_none());

            //     leaf_guard=get_right_sibling_ptr(&node).map(|ptr|table.get_page(ptr));
            // }
            
        }
    }

}