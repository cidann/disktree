use std::{ cmp::Ordering, collections::btree_map::Keys, error, marker::PhantomData, mem::{size_of, size_of_val}, ops::{Bound, Deref, DerefMut, RangeBounds, Shl}, process::id, str::from_utf8};
use core::array;
use byteorder::{BigEndian, ByteOrder, WriteBytesExt};
use cursor::Cursor;
use log::warn;
use proptest::bits::BitSetLike;
use thiserror::Error;

use crate::{tree::node::utils::{create_key_val_offset, get_key_val_offset}, utils::{offset_buffer, offset_buffer_mut, range_buffer_mut, read_u16_with_idx, read_u64_with_idx, shift_left_and_write, shift_right_and_write, write_u16_with_idx, write_u64_with_idx}};
use crate::utils::{assert_try_into, range_array,TupleAssertTryFrom, read_u32_with_idx, write_u32_with_idx};

use self::{iter::{EntryRefIter, EntryRefIterMut, OffsetIterMut}, key_cmp::KeyCmp};

mod utils;
pub mod key_cmp;
pub mod iter;
pub mod cursor;

/*
/////////////////////////////////////////////////////////////////////////////////////////////
/ flags | len | ptrs | (key_end_offset1,val_end_offset1),(key_end_offset2,val_end_offset2), /
/ (key_end_offset3,val_end_offset3),...,(new_key_end,0)|                                    /
/                                                                                           /
/                                                                                           /
/                                                   ...,(val3,key3),(val2,key2),(val1,key1) /
//////////////////////////////////////////////////////////////////////////////////////////////
*/

const MIN_PG_SIZE:usize=2usize.pow(11);
const META_DATA_SIZE:usize=size_of::<MetaDataBytes>();
const OFFSET_SIZE:usize=size_of::<OffsetBytes>();
const RESERVED_SIZE:usize=META_DATA_SIZE+OFFSET_SIZE;

pub const MIN_ENTRY:usize=4;

// Byte Count: flags:2 len:2 ptrs:16
pub type NodeFlagBytes=[u8;2];
pub type NodeLenBytes=[u8;2];
pub type MetaDataBytes=[u8;20];
pub type OffsetBytes=[u8;4];

type NodeEndian=BigEndian;
pub trait NodeData:Deref<Target = [u8]>{}
pub trait MutNodeData:NodeData+DerefMut<Target = [u8]>{}

#[derive(Error,Debug)]
pub enum OpError{
    #[error("The node does not have enough space for operation")]
    OutOfSpace,
    #[error("The entry size exceeded the limit")]
    EntrySizeExceed,
    #[error("Broken invariant encountered during operation")]
    InvariantError
}

/// Zero Copy Node holding slice of page data
/// The keys and values are expected to be encrypted into byte slices
/// which will be compared lexicologically when needed
/// All data is stored in big endian order
pub struct Node<T,KC>
where
    T:NodeData,
    KC:KeyCmp
{
    data:T,
    phantom:PhantomData<KC>
}


impl<T,KC> Node<T,KC>
where
    T:NodeData,
    KC:KeyCmp
{   
    /// Parse the buffer into a node in place. This function is considered
    /// to be very cheap so that self referential structs are not needed
    /// and data can be parsed each time it needs to perform node operation.
    /// 
    /// #Panics
    /// This function panics if the slice is not at least MIN_PG_SIZE
    /// or some assumption about buffer content is violated and detected
    /// It also panics if the data was detected to not be initialized
    /// if bouding offset is 0 although if the buffer was filled with 
    /// random data, the function might not panic.
    /// #Safety
    /// This function assume the data in the buffer is well formed for the node
    pub fn parse(data:T)->Node<T,KC>{
        debug_assert!(data.len()>=MIN_PG_SIZE,"Expected buffer of at least {} bytes got buffer of {} bytes",MIN_PG_SIZE,data.len());
    
        //Initialize value bound if length is zero
        let node=Node{
            data,
            phantom:PhantomData
        };

        debug_assert_ne!(node.key_val_bound().0,0);

        node
    }

    /// Get the value slice for the key slice
    pub fn get(&self,key:&[u8])->Option<&[u8]>{
        let idx=self.binary_search(key).ok()?;
        
        Some(self.get_val_slice_at(idx))
    }

    /// Iterator that yields reference to key/val entry within the range
    /// 
    /// If the range is invalid and does not cover any keyspace,
    /// An iterator that yields nothing is returned
    pub fn range<'b,R>(&self,range:R)->EntryRefIter<T,KC>
    where
        R:RangeBounds<&'b[u8]>
    {
        let start=range.start_bound();
        let end=range.end_bound();
        if let (Some(start_idx),Some(end_idx))=(self.lower_bound_idx(start),self.upper_bound_idx(end)){
            // EntryRefIter accepts range where start>end where it yields nothing
            EntryRefIter::new(start_idx..=end_idx, self)
        }
        else {
            EntryRefIter::new(0..0, self)
        }

    }

    /// Return Cursor pointing at gap after the bounded
    /// entry. If no entry is bounded then the cursor points
    /// to the gap before the first entry
    pub fn upper_bound(&self,bound:Bound<&&[u8]>)->Cursor<T,KC>{
        match self.upper_bound_idx(bound) {
            Some(idx) => {
                Cursor::new(idx+1, self)
            },
            None => {
                Cursor::new(0, self)
            },
        }
    }

    /// Return Cursor pointing at gap before the bounded
    /// entry. If no entry is bounded then the cursor points
    /// to the gap after the last entry
    pub fn lower_bound(&self,bound:Bound<&&[u8]>)->Cursor<T,KC>{
        match self.lower_bound_idx(bound) {
            Some(idx) => {
                Cursor::new(idx, self)
            },
            None => {
                Cursor::new(self.len(), self)
            },
        }
    }

    /// Get the entry with smallest key
    pub fn first(&self)->Option<(&[u8],&[u8])>{
        if self.len()>0{
            Some(self.get_key_val_slices_at(0))
        }
        else{
            None
        }
    }

    /// Get the entry with largest key
    pub fn last(&self)->Option<(&[u8],&[u8])>{
        if self.len()>0{
            Some(self.get_key_val_slices_at(self.len()-1))
        }
        else{
            None
        }
    }

    /// Iterator that yields reference to key/val entry bytes
    pub fn iter(&self)->EntryRefIter<T,KC>{
        EntryRefIter::new(0..self.len(),self)
    }
    
    /// Get the flags for the node
    pub fn get_flags(&self)->u16{
        read_u16_with_idx::<NodeEndian>(&self.data, 0)
    }

    /// Get the extra pointers for the node
    pub fn get_ptrs(&self)->(u64,u64){
        let offset_buf=&self.data[size_of::<NodeFlagBytes>()+size_of::<NodeLenBytes>()..];
        (read_u64_with_idx::<NodeEndian>(offset_buf, 0),read_u64_with_idx::<NodeEndian>(offset_buf, 1))
    }

    /// Check if this node has enough space to insert a entry
    /// with the given size
    pub fn enough_size(&self,size:usize)->bool{
        self.space_remain()>=size+OFFSET_SIZE
    }

    /// Check if the node's data space utilization is 
    /// below the ratio
    pub fn is_underflow(&self,ratio:f64)->bool{
        assert!(ratio<1f64);
        let underflow_size=(self.data_space() as f64 * ratio) as usize;
        let space_used=self.data_space()-self.space_remain();
        space_used < underflow_size
    }

    /// Get number of entries
    pub fn len(&self)->usize{
        read_u16_with_idx::<NodeEndian>(&self.data, 1) as usize
    }
    
    /// Get slice that represents the ith key 
    /// panics if idx>=self.len()
    pub fn get_key_slice_at(&self,i:usize)->&[u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (key_right,val_right)=self.get_offset_at(i);
        
        &self.data[val_right+1..=key_right]
    }

    /// Get slice that represents the ith value 
    /// panics if idx>=self.len()
    pub fn get_val_slice_at(&self,i:usize)->&[u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (_,value_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        &self.data[next_key_right + 1 ..= value_right]
    }

    /// Get two slice that represents the ith key/val  
    /// panics if idx>=self.len()
    pub fn get_key_val_slices_at(&self,i:usize)->(&[u8],&[u8]){
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (key_right,val_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        (&self.data[val_right + 1 ..= key_right],&self.data[next_key_right+1..=val_right])
    }

    /// Get the number of bytes remaining for entry and offset
    fn space_remain(&self)->usize{
        if self.len()==0{
            self.data_space()
        }
        else {
            // Get the offset at self.len() which does not contain real data
            // and acts as boundry for the true last key/val
            let (next_key_offset,_)=self.key_val_bound();
            //dbg!(self.get_flags(),self.len());
            // if next_key_offset>=4096{
            //     (0..=self.len())
            //     .map(|v|self.get_offset_at(v))
            //     .enumerate()
            //     .for_each(|(i,(k,v))|println!("{i} {} {k},{v}",self.len()*OFFSET_SIZE));
            // }
            let key_val_space_used=self.data.len()-1-next_key_offset;

            self.data_space()-self.len()*OFFSET_SIZE-key_val_space_used
        }
    }

    /// Get the number of bytes the node use for entries and their offset
    fn data_space(&self)->usize{
        self.data.len()-META_DATA_SIZE-OFFSET_SIZE
    }

    /// Binary search the node for key
    /// Result::Ok is returned with the offset index if found.
    /// Otherwise Result::Err is returned with the offset index where
    /// the new key/val offset should be inserted to maintain order
    fn binary_search(&self,key:&[u8])->Result<usize, usize>{
        let mut left:i32=0;
        let mut right:i32=assert_try_into::<_,i32>(self.len())-1;
        while left<=right {
            let mid=(left+right)/2;
            match KC::cmp(key,self.get_key_slice_at(assert_try_into(mid))) {
                Ordering::Less => {
                    right=mid-1;
                },
                Ordering::Equal => return Ok(assert_try_into(mid)),
                Ordering::Greater => {
                    left=mid+1;
                },
            } 
        }
        
        Err(assert_try_into(right+1))
    }

    /// return index of entry with largest key at or
    /// before the given bound. Unbounded returns largest
    /// index in node
    /// If no entry is upper bounded by given bound, 
    /// None is returned
    fn upper_bound_idx(&self,bound:Bound<&&[u8]>)->Option<usize>{
        match bound {
            Bound::Included(key) => {
                match self.binary_search(key) {
                    Ok(idx) => {
                        Some(idx)
                    },
                    Err(idx) => {
                        idx.checked_sub(1)
                    },
                }
            },
            Bound::Excluded(key) => {
                match self.binary_search(key) {
                    Ok(idx)|Err(idx) => {
                        idx.checked_sub(1)
                    },
                }
            },
            Bound::Unbounded => {
                self.len().checked_sub(1)
            },
        }
    }

    /// return index of entry with smallest key at or
    /// after the given bound. Unbounded returns smallest
    /// index in node
    /// If no entry is lower bounded by given bound, 
    /// None is returned
    fn lower_bound_idx(&self,bound:Bound<&&[u8]>)->Option<usize>{
        let idx=match bound {
            Bound::Included(key) => {
                match self.binary_search(key) {
                    Ok(idx)|Err(idx) => {
                        idx
                    },
                }
            },
            Bound::Excluded(key) => {
                match self.binary_search(key) {
                    Ok(idx) => {
                        idx+1
                    },
                    Err(idx) => {
                        idx
                    },
                }
            },
            Bound::Unbounded => {
                0
            },
        };

        if idx<self.len(){
            Some(idx)
        }
        else {
            None
        }
    }
    
    /// Return the offset of the byte that bounds the 
    /// last key/val. Or simply the offset that will be used for the 
    /// next key/val.
    fn key_val_bound(&self)->(usize,usize){
        self.get_offset_at(self.len())
    }

    /// Get ith key/val offset 
    /// No checks performed so if ith offset is not
    /// properly formated, it is undefined behavior
    fn get_offset_at(&self,i:usize)->(usize,usize){
        let (key_off,val_off) = get_key_val_offset(
            read_u32_with_idx::<NodeEndian>(self.skip_metadata_slice(), i)
        );

        (key_off as usize, val_off as usize)
    }

    /// Get slice that contains the offsets including the bounding offset
    fn skip_metadata_slice(&self)->&[u8]{
        &self.data[META_DATA_SIZE..]
    }
}

impl<T,KC> Node<T,KC>
where
    T:MutNodeData,
    KC:KeyCmp
{
    /// Initialized the buffer as a node in place
    /// #Panics
    /// This function panics if the slice is not at least MIN_PG_SIZE
    /// or some assumption about buffer content is violated and detected
    /// #Safety
    /// This function is only safe if the bytes in the buffer are zeros
    pub fn new(data:T)->Node<T,KC>{
        assert!(data.len()>=MIN_PG_SIZE,"Expected buffer of at least {} bytes got buffer of {} bytes",MIN_PG_SIZE,data.len());
   
        let bound_offset=assert_try_into(data.len()-1);

        //Initialize value bound if length is zero
        let mut node=Node{
            data,
            phantom:PhantomData
        };
        assert_eq!(node.len(),0);

        write_u32_with_idx::<NodeEndian>(
            node.skip_metadata_slice_mut(),
            0,
            create_key_val_offset(
                bound_offset,
                bound_offset
            )
        );
    
        node
    }

    /// Get the mutable value slice for the key slice
    pub fn get_mut(&mut self,key:&[u8])->Option<&mut [u8]>{
        let idx=self.binary_search(key).ok()?;
        
        Some(self.get_val_slice_at_mut(idx))
    }
    
    /// Insert the key/val entry into the node if there is enough space.
    /// If the key already exist, the old value is returned in Vec<u8>
    /// An error is returned if the entry size exceeded limit or if
    /// there is not enough space left
    pub fn insert(&mut self,key:&[u8],val:&[u8])->Result<Option<Vec<u8>>,OpError>{
        if key.len()+val.len()>node_entry_size_limit(self.data.len()){
            Err(OpError::EntrySizeExceed)
        }
        else if !self.enough_size(key.len()+val.len()){
            Err(OpError::OutOfSpace)
        }
        else {
            let (prev_val,idx,shift)=match self.binary_search(key) {
                // Replace val for key
                Ok(idx) => {
                    //dbg!("Replace Node entry ",idx);
                    let cur=Vec::from(self.get_val_slice_at(idx));
                    let size_diff=assert_try_into::<_,i16>(val.len())-assert_try_into::<_,i16>(cur.len());
                    let (key_bound,_)=self.key_val_bound();
                    let (cur_key_right,cur_val_right)=self.get_offset_at(idx);
                    let (next_key_right,_)=self.get_offset_at(idx+1);
                    // Shift all entries with greater key to 
                    // make space or fill empty space from updated value
                    match size_diff {
                        shift @ ..=-1 => {
                            let right_shift:usize=assert_try_into(shift.checked_abs().unwrap());
                            self.data[key_bound+1..=next_key_right+right_shift].rotate_right(right_shift);
                        },
                        shift @ 1.. => {
                            let left_shift:usize=assert_try_into(shift);
                            self.data[key_bound+1-left_shift..=next_key_right].rotate_left(left_shift);
                        },
                        0=>{}
                    }
                    
                    // Update value
                    self.data[cur_val_right - val.len()+1..=cur_val_right].copy_from_slice(val);

                    (Ok(Some(cur)),idx,size_diff)
                },
                // Insert val and key at offset idx
                Err(idx) => {
                    //dbg!("News Node entry ",idx);
                    // For the shifting part, it performs the same logic
                    // as if updating a value with length 0 to be a value that is
                    // key.len() + val.len() and insert the new offset for the new entry
                    let (key_bound,_)=self.key_val_bound();
                    let (next_key_right,next_val_right)=self.get_offset_at(idx);
                    let new_key_right=next_key_right;
                    let new_val_right: usize=next_key_right-key.len();
                    let key_val_bytes=[val,key].concat();
                    let mut new_offset=Vec::new();
                    new_offset.write_u32::<NodeEndian>(
                        create_key_val_offset(
                            assert_try_into(new_key_right),
                            assert_try_into(new_val_right)
                        )
                    ).unwrap();
                    
                    // Insert new key/value
                    self.left_shift_and_insert(key_bound+1, next_key_right, &key_val_bytes);
                    
                    // Insert new offset and update length
                    let new_len=self.len()+1;
                    shift_right_and_write(
                        range_buffer_mut::<OffsetBytes>(self.skip_metadata_slice_mut(), idx, new_len+1),
                        &new_offset
                    );
                    self.set_len(assert_try_into(new_len));

                    (Ok(None),idx,assert_try_into(key_val_bytes.len()))
                }
            };

            // Update key/value offset for larger keys entries after update/insert
            let bound_idx=self.len();
            for (idx,offset) in self.offset_iter().enumerate().skip(idx+1){
                let (key_offset,val_offset)=<(i16,i16)>::assert_try_from(
                    get_key_val_offset(NodeEndian::read_u32(offset))
                );
                let new_offset= if idx!=bound_idx{
                    create_key_val_offset(
                        assert_try_into(key_offset-shift),
                        assert_try_into(val_offset-shift)
                    )
                }
                else{
                    create_key_val_offset(assert_try_into(key_offset-shift),0)
                };
                NodeEndian::write_u32(offset, new_offset);
            }

            let (k,v)= self.get_offset_at(self.len());
            //dbg!(self.get_flags(),k,v,key.len(),val.len());
            // (0..=self.len())
            // .map(|v|self.get_offset_at(v))
            // .enumerate()
            // .for_each(|(i,(k,v))|println!("{i} {} {k},{v}",self.len()*OFFSET_SIZE));
            // if k>4095 {
            //     panic!("")
            // }
            prev_val
        }
    }

    /// Removes the entry with the key and return
    /// old value in Vec<u8> if there was any
    pub fn remove(&mut self,key:&[u8])->Option<Vec<u8>>{
        match self.binary_search(key){
            Ok(idx) => {
                let old_val=Vec::from(self.get_val_slice_at(idx));
                let (key_right,val_right)=self.get_offset_at(idx);
                let (next_key_right,next_val_right)=self.get_offset_at(idx+1);
                let (key_bound,_)=self.key_val_bound();
                let entry_size=key_right-next_key_right;

                // Remove entry and shift larger entries 
                self.right_shift_and_insert(key_bound+1, next_key_right, &[0].repeat(entry_size));
                
                // Remove offset and reduce len
                let cur_len=self.len();
                shift_left_and_write(
                    range_buffer_mut::<OffsetBytes>(self.skip_metadata_slice_mut(), idx, cur_len+1), 
                    &[0].repeat(OFFSET_SIZE)
                );
                self.set_len(assert_try_into(cur_len-1));

                //Change offset for all larger entries which 
                //now have idx-1
                let bound_idx=self.len();
                for (idx,offset) in self.offset_iter().enumerate().skip(idx){
                    let (key_offset,val_offset)=<(i16,i16)>::assert_try_from(
                        get_key_val_offset(NodeEndian::read_u32(offset))
                    );
                    let new_offset= if idx!=bound_idx{
                        create_key_val_offset(
                            assert_try_into(key_offset+assert_try_into::<_,i16>(entry_size)),
                            assert_try_into(val_offset+assert_try_into::<_,i16>(entry_size))
                        )
                    }
                    else{
                        create_key_val_offset(assert_try_into(key_offset+assert_try_into::<_,i16>(entry_size)),0)
                    };

                    NodeEndian::write_u32(offset, new_offset);
                }

                Some(old_val)
            },
            Err(idx) => {
                None
            },
        }
    }

    /// Iterator that yields mutable reference to key/val entry bytes
    pub fn iter_mut(&mut self)->EntryRefIterMut{
        EntryRefIterMut::new(0..self.len(),self)
    }

    /// Set the flags for the node
    pub fn set_flags(&mut self,flag:u16){
        write_u16_with_idx::<NodeEndian>(&mut self.data, 0, flag);
    }

    /// Set the ptrs for the node
    pub fn set_ptrs(&mut self,ptr1:u64,ptr2:u64){
        let offset_buf=&mut self.data[size_of::<NodeFlagBytes>()+size_of::<NodeLenBytes>()..];
        write_u64_with_idx::<NodeEndian>(offset_buf, 0, ptr1);
        write_u64_with_idx::<NodeEndian>(offset_buf, 1, ptr2);
    }

    /// Split the node by bytes so that this node will have
    /// around the first half bytes of entries and the other node 
    /// will have around the second half bytes of entries. 
    /// It is Guaranteed that this node and the other node will
    /// have enough space for at least 1 more entry within the maximum
    /// size limit
    /// #Panics
    /// Panics if this node have less than two entries
    /// or if the other node is not empty since its
    /// likely a bug in usage
    /// #Safety
    /// Both nodes are assumed to be well formed
    pub fn split<D>(&mut self,other:&mut Node<D,KC>)
    where
        D:MutNodeData
    {
        assert!(self.len()>=2,"Less than two entry at split");
        assert_eq!(other.len(),0,"Other node not empty");
        let (start_key_right,_)=self.get_offset_at(0);
        let (bound_key_right,_)=self.key_val_bound();
        let total_entry_size=start_key_right-bound_key_right;
        let total_offset_size=size_of::<OffsetBytes>()*self.len();
        let total_size=total_entry_size+total_offset_size;
        let mid_size=total_size/2;

        let mut size_iter=self
        .iter()
        .map(|(k,v)|k.len()+v.len()+size_of::<OffsetBytes>())
        .scan(0, |acc,size|{
            *acc+=size;
            Some(*acc)
        })
        .enumerate();

        //Idx of last entry to keep
        let (split_idx,new_total_size)=size_iter
        .find(|(idx,size)|*size>=mid_size)
        .expect("Expected mid size to be elapse in iteration of accumulation of size");
        assert_eq!(size_iter.last().expect("No entries split out").1,total_size);

        //assert!(self.len()-split_idx>1,"No entries split out");

        // For now just insert every entry. This can be improved by
        // Manual memory manipulation
        for (k,v) in EntryRefIter::new(split_idx+1..,self){
            other.insert(k, v).unwrap();
        }

        //Its safe to just set length without changing bounding offset
        //since the previous entry's key right offset can be used as bound
        let old_len=self.len();
        self.set_len(assert_try_into(split_idx+1));
        
        assert!(self.enough_size(node_entry_size_limit(self.data.len())));
        assert!(other.enough_size(node_entry_size_limit(other.data.len())));
    }

    /// Copy all entries from other node into current node.
    /// Panics if the current node don't have enough space.
    pub fn append<D>(&mut self,other:&mut Node<D,KC>)
    where
        D:MutNodeData
    {
        let space_used=other.data_space()-other.space_remain();
        assert!(self.enough_size(space_used));
        // Just insert everything for now
        for (k,v) in other.iter(){
            self.insert(k, v).unwrap();
        }
    }

    /// Get mutable slice that represents the ith value 
    /// panics if idx>=self.len()
    pub fn get_val_slice_at_mut(&mut self,i:usize)->&mut [u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (_,value_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        &mut self.data[next_key_right + 1 ..= value_right]
    }

    /// Get two slice that represents the ith key/val  
    /// panics if idx>=self.len()
    pub fn get_key_val_slices_at_mut(&mut self,i:usize)->(&[u8],&mut [u8]){
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (key_right,val_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        let entry=&mut self.data[next_key_right+1..=key_right];
        let (key,val)=entry.split_at_mut(val_right-(next_key_right+1));
        (key,val)
    }

    /// Update the length of node on the data page and data structure
    fn set_len(&mut self,len:u16){
        write_u16_with_idx::<NodeEndian>(&mut self.data, 1, len);
    }

    /// Shifts the data over the range (start..=end)
    /// to (start-data.len()..=end-data.len())
    /// The data at the shifted to location is overwritten
    /// and the input data is written to old location.
    /// 
    /// #Panics
    /// Panics with out of bound if source range
    /// or destination range is out of bound.
    /// Logical errors are silent
    fn left_shift_and_insert(&mut self,start:usize,end:usize,data:&[u8]){
        shift_left_and_write(&mut self.data[start-data.len()..=end], data);
    }

    /// Shifts the data over the range (start..=end)
    /// to (start+data.len()..=end+data.len())
    /// The data at the shifted to location is overwritten
    /// and the input data is written to old location.
    /// 
    /// #Panics
    /// Panics with out of bound if source range
    /// or destination range is out of bound.
    /// Logical errors are silent
    fn right_shift_and_insert(&mut self,start:usize,end:usize,data:&[u8]){
        shift_right_and_write(&mut self.data[start..=end+data.len()], data);
    }

    fn offset_iter(&mut self)->OffsetIterMut{
        OffsetIterMut::new(self)
    }
    /// Get mutable slice that contains the offsets including the bounding offset
    fn skip_metadata_slice_mut(&mut self)->&mut [u8]{
        &mut self.data[META_DATA_SIZE..]
    }
}


/// Get the max number of bytes an entry inclduing
/// its offset can have given the node size
pub fn node_entry_size_limit(size:usize)->usize{
    (size-RESERVED_SIZE)/MIN_ENTRY-OFFSET_SIZE
}

impl NodeData for &[u8] {}
impl NodeData for &mut [u8] {}
impl MutNodeData for &mut [u8] {}



#[cfg(test)]
mod old_tests;

#[cfg(test)]
mod tests{
    use core::panic;
    use std::{borrow::Borrow, clone, cmp::Reverse, collections::{ BTreeMap, BinaryHeap, VecDeque}, iter::{repeat, repeat_with}, ops::{self, Deref}};
    use crate::utils::{generate_indexex, generate_string};
    use self::key_cmp::Lexicological;
    use super::*;
    use crate::utils::*;
    use proptest::prelude::*;
    use rand::{seq::SliceRandom, thread_rng};

    #[test]
    #[should_panic]
    fn new_invalid_size(){
        let mut data=vec![0;1000];
        Node::<_,Lexicological>::new(data.as_mut_slice());
    }

    #[test]
    fn test_metadata(){
        let mut data=vec![0;4096];
        let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);
        assert_eq!(node.get_flags(),0);
        node.set_flags(12);
        assert_eq!(node.get_flags(),12);
        node.set_ptrs(u64::MAX, 1);
        assert_eq!(node.get_ptrs(),(u64::MAX, 1));
    }

    #[test]
    fn insert_test_internal1(){
        let mut data=vec![0;4096];
        let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);
        let mut test_data:Vec<usize>=(0..(4096-META_DATA_SIZE-OFFSET_SIZE)/(OFFSET_SIZE+16)).collect();
        test_data.shuffle(&mut thread_rng());
        for (i,v) in test_data.iter().enumerate(){
            node.insert(&v.to_be_bytes(), &v.to_be_bytes()).unwrap();
            assert_eq!(node.space_remain(),4096-META_DATA_SIZE-OFFSET_SIZE-(i+1)*(OFFSET_SIZE+16));
            assert_eq!(node.len(),i+1);
        }
        assert!(node.insert("abcd".repeat(2).as_bytes(),"abcd".repeat(2).as_bytes()).is_err());
        assert!(node.insert("abcd".as_bytes(),"abcd".as_bytes()).is_ok());
        assert_eq!(node.space_remain(),0);

        let (mut counter_k,mut counter_v)=(0,0);
        for (k,v) in node.iter(){
            if k.len()==8{
                assert_eq!(usize::from_be_bytes(k.try_into().unwrap()),counter_k);
                assert_eq!(usize::from_be_bytes(v.try_into().unwrap()),counter_v);
                counter_k+=1;
                counter_v+=1;
            }
            else {
                assert_eq!(String::from_utf8(k.to_vec()).unwrap(),"abcd");
                assert_eq!(String::from_utf8(v.to_vec()).unwrap(),"abcd");
            }
        }

        test_data.shuffle(&mut thread_rng());
        for i in test_data{
            assert_eq!(node.get(&i.to_be_bytes()).unwrap(),i.to_be_bytes());
        }


    }

    #[test]
    fn insert_test_internal2(){
        let mut data=vec![0;4096];
        let mut node:Node<&mut _,Lexicological>=Node::new(&mut data);
        assert!(node.insert("abc".repeat(1000).as_bytes(), "".as_bytes()).is_err());
        assert_eq!(node.space_remain(),4096-META_DATA_SIZE-OFFSET_SIZE);
        assert!(node.insert("abc".repeat(300).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.insert("abc".repeat(300).as_bytes(), "".as_bytes()).unwrap().unwrap(),"".as_bytes());
        assert_eq!(node.len(),1);
        assert!(node.insert("123".repeat(300).as_bytes(), "".as_bytes()).is_ok());
        assert!(node.insert("456".repeat(300).as_bytes(), "".as_bytes()).is_ok());
        assert!(node.insert("789".repeat(300).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.len(),4);
        assert!(node.insert("!!!".repeat(200).as_bytes(), "".as_bytes()).is_err());
        assert!(node.space_remain()<600);
        assert_eq!(node.len(),4);
        assert!(node.insert("!!!".repeat(100).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.len(),5);
        
        let mut q:VecDeque<usize>=VecDeque::from(vec![300,900,900,900,900]);
        let mut h=BinaryHeap::from(["!!!","abc","123","456","789"].map(Reverse));

        for (k,v) in node.iter(){
            assert_eq!(v.len(),0);
            assert_eq!(k.len(),q.pop_front().unwrap());
            assert_eq!(&k[..3],h.pop().unwrap().0.as_bytes());
        }

    }
    
    #[test]
    fn remove_test1(){
        let mut data=[0].repeat(4096);
        let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);
        let input_generator=repeat_with(||{
            (generate_string(1..11),generate_string(1..11))
        });
        let mut inputs=BTreeMap::new();

        input_generator
        .take_while(|(k,v)|{
            if let Ok(old_v)=node.insert(k.as_bytes(), v.as_bytes()){
                inputs.insert(k.clone(),v.clone());
                true
            }
            else {
                false
            }
        })
        .count();
        dbg!(inputs.len());
        assert!(node.space_remain()<20+size_of::<OffsetBytes>());

        let remove_indexex=generate_indexex(0..node.len());
        let remove_key:Vec<&String>=inputs
        .keys()
        .enumerate()
        .filter(|(i,key)|remove_indexex.contains(i))
        .map(|(i,k)|k)
        .collect();
        
        let before_len=node.len();
        for key in remove_key{
            node.get(key.as_bytes()).unwrap();
            node.remove(key.as_bytes()).unwrap();
        }
        dbg!(node.len(),before_len,remove_indexex.len());
        assert_eq!(node.len(),before_len-remove_indexex.len());

    }

    proptest!{
        #[test]
        fn prop_std_btree((pairs,get,remove,range) in generate_kv_strategy(20,500)){
            btree_ops(pairs,get,remove,range);
        }

        #[test]
        fn prop_parsed_std_btree((pairs,get,remove,range) in generate_kv_strategy(20,500)){
            prop_parsed_std_btree_impl(pairs, get, remove, range);
        }
    }
    fn prop_parsed_std_btree_impl(pairs:Vec<(String,String)>,get:Vec<usize>,remove:Vec<usize>,range:Vec<(String,String)>){

        let pairs_ref:Vec<_>=pairs.iter().map(|(k,v)|(k.borrow(),v.borrow())).collect();
        let get_ref:Vec<_>=get.iter().map(|idx|pairs_ref[*idx].0).collect();
        let remove_ref:Vec<_>=remove.iter().map(|idx|pairs_ref[*idx].0).collect();
        let range_ref:Vec<_>=range.iter().map(|(k,v)|(k.borrow(),v.borrow())).collect();

        let mut data=[0].repeat(4096);
        let mut tree=BTreeMap::new();
        {
            let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);

            prop_insert(&mut node,&mut tree,&pairs_ref);
            prop_get(&mut node, &mut tree, &get_ref);
            prop_remove(&mut node, &mut tree, &remove_ref);
            prop_range(&mut node, &mut tree, &range_ref);
        }
        let mut node:Node<&mut [u8],Lexicological>=Node::parse(&mut data);
        
        prop_get(&mut node, &mut tree, &get_ref);
        prop_range(&mut node, &mut tree, &range_ref);
    }

    fn prop_insert(node:&mut Node<&mut [u8],Lexicological>,tree:&mut BTreeMap<String,String>,pairs:&[(&str,&str)]){
        assert_eq!(node.len(),tree.len());
        for (k,v) in pairs.iter().copied().inspect(|_|{}){
            match node.insert(k.as_bytes(), v.as_bytes()) {
                Ok(res) =>{
                    let std_res=tree.insert(k.to_owned(), v.to_owned());
                    match res {
                        Some(old_v) => {
                            assert_eq!(old_v,std_res.unwrap().as_bytes());
                        },
                        None => {
                            assert!(std_res.is_none());
                        },
                    }
                },
                Err(e) => {
                    assert!(!matches!(e,OpError::InvariantError));
                },
            }
        }
        assert_eq!(node.len(),tree.len());
    }

    fn prop_remove(node:&mut Node<&mut [u8],Lexicological>,tree:&mut BTreeMap<String,String>,keys:&[&str]){
        assert_eq!(node.len(),tree.len());
        for k in keys.iter().copied(){
            assert_eq!(node.remove(k.as_bytes()),tree.remove(k).map(Vec::from));
            assert_eq!(node.len(),tree.len());
        }
        assert_eq!(node.len(),tree.len());
    }

    fn prop_get(node:&mut Node<&mut [u8],Lexicological>,tree:&mut BTreeMap<String,String>,keys:&[&str]){
        assert_eq!(node.len(),tree.len());
        for k in keys.iter().copied(){
            assert_eq!(node.get(k.as_bytes()),tree.get(k).map(|v|v.as_bytes()));
        }
    }

    fn prop_range(node:&mut Node<&mut [u8],Lexicological>,tree:&mut BTreeMap<String,String>,range:&[(&str,&str)]){
        assert_eq!(node.len(),tree.len());
        for (start,end) in range.iter().cloned().map(|(k,v)|(k.to_owned(),v.to_owned())){
            let std_iter=tree
            .range::<String,_>(&start..&end)
            .map(|(k,v)|(k.as_bytes(),v.as_bytes()));
            
            let node_itr=node.range(start.as_bytes()..end.as_bytes());
    
            assert!(std_iter.eq(node_itr))
        }
    }

    fn btree_ops(pairs:Vec<(String,String)>,get:Vec<usize>,remove:Vec<usize>,range:Vec<(String,String)>){
        let mut std_tree:BTreeMap<String, String>=BTreeMap::new();
        let mut data=[0].repeat(4096);
        let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);
        
        for (k,v) in pairs.iter(){
            match node.insert(k.as_bytes(), v.as_bytes()) {
                Ok(res) =>{
                    let std_res=std_tree.insert(k.clone(), v.clone());
                    match res {
                        Some(old_v) => {
                            assert_eq!(old_v,std_res.unwrap().as_bytes());
                        },
                        None => {
                            assert!(std_res.is_none());
                        },
                    }
                },
                Err(e) => {
                    assert!(!matches!(e,OpError::InvariantError));
                },
            }
        }
        dbg!(std_tree.len(),node.len());
        dbg!(range.len());

        let std_iter=std_tree
        .iter_mut()
        .map(|(k,v)|(k.as_bytes(),v.as_bytes()));
        let node_iter=node.iter_mut().map(|(k,v)|(k,&*v));
        assert!(std_iter.eq(node_iter));

        let std_iter=std_tree
        .iter()
        .map(|(k,v)|(k.as_bytes(),v.as_bytes()));
        let node_iter=node.iter_mut().map(|(k,v)|(k,&*v));
        assert!(std_iter.eq(node_iter));
    
        for (start,end) in range{
            let std_iter=std_tree
            .range::<String,_>(&start..&end)
            .map(|(k,v)|(k.as_bytes(),v.as_bytes()));
            
            let node_itr=node.range(start.as_bytes()..end.as_bytes());
    
            assert!(std_iter.eq(node_itr))
        }
    
        for (get,remove) in get.iter().zip(&remove){
            let (get_key,remove_key)=(pairs[*get].0.clone(),pairs[*remove].0.clone());
            assert_eq!(node.get(get_key.as_bytes()),std_tree.get(&get_key).map(|s|s.as_bytes()));
            assert_eq!(node.remove(remove_key.as_bytes()),std_tree.remove(&remove_key).map(Vec::from));
            assert_eq!(node.len(),std_tree.len());
        }
        dbg!(std_tree.len(),node.len());
    }
}