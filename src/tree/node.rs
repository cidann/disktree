use std::{ cmp::Ordering, collections::btree_map::Keys, error, marker::PhantomData, mem::{size_of, size_of_val}, ops::Shl, process::id};
use core::array;
use byteorder::{BigEndian, ByteOrder, WriteBytesExt};
use thiserror::Error;

use crate::{tree::node::utils::{create_key_val_offset, get_key_val_offset}, utils::{offset_buffer_mut, range_buffer_mut, read_u16_with_idx, shift_left_and_write, shift_right_and_write, write_u16_with_idx}};
use crate::utils::{assert_try_into, range_array,TupleAssertTryFrom, read_u32_with_idx, write_u32_with_idx};

use self::{iter::EntryRefIter, key_cmp::KeyCmp};

mod utils;
pub mod key_cmp;
pub mod iter;

/*
//////////////////////////////////////////////////////////////////////////////////////////
/ flags | len | (key_end_offset1,val_end_offset1),(key_end_offset2,val_end_offset2),     /
/ (key_end_offset3,val_end_offset3),...,(new_key_end,0)|                                 /
/                                                                                        /
/                                                                                        /
/                                                ...,(key3,val3),(key2,val2),(key1,val1) /
//////////////////////////////////////////////////////////////////////////////////////////
*/

const PG_SIZE:usize=4096;
const META_DATA_SIZE:usize=size_of::<MetaDataBytes>();
const OFFSET_SIZE:usize=size_of::<OffsetBytes>();
const MAX_PG_ENTRY:usize=(PG_SIZE-META_DATA_SIZE)/2/OFFSET_SIZE-1;
const MAX_ENTRY_SIZE:usize=(PG_SIZE-META_DATA_SIZE)/3;

const OFFSET_INDEX_ARRAY:[usize;MAX_PG_ENTRY]=range_array::<0,MAX_PG_ENTRY>();


type Endian=BigEndian;

pub type MetaDataBytes=u32;
pub type OffsetBytes=u32;

#[derive(Error,Debug)]
pub enum OpError{
    #[error("The node does not have enough space for operation")]
    OutOfSpace,
    #[error("The node reached max entry count")]
    MaxEntry,
    #[error("The entry size exceeded the limit")]
    EntrySizeExceed,
    #[error("Broken invariant encountered during operation")]
    InvariantError
}



/// Zero Copy Node holding slice of page data
/// The keys and values are expected to be encrypted into byte slices
/// which will be compared lexicologically when needed
/// All data is stored in big endian order
pub struct Node<'a,KC>
where
    KC:KeyCmp
{
    data:&'a mut [u8],
    phantom:PhantomData<KC>
}

impl<'a,KC> Node<'a,KC>
where
    KC:KeyCmp
{
    /// parse a page of PG_SIZE bytes into a node in place. 
    /// #Panics
    /// This function panics if the slice is not exactly PG_SIZE
    pub fn parse(data:&'a mut [u8])->Node<KC>{
        assert_eq!(data.len(),PG_SIZE,"Expected data size {} to match page size {}",data.len(),PG_SIZE);
   
        let mut node=Node{
            data,
            phantom:PhantomData
        };
        assert!(node.len() as usize<=MAX_PG_ENTRY,"Number of entries {} exceeded limit {}",node.len(),MAX_PG_ENTRY);

        //Initialize value bound if length is zero
        let bound_offset=assert_try_into(PG_SIZE-1);
        if node.len()==0{
            write_u32_with_idx::<Endian>(
                node.get_offset_slice_mut(),
                0,
                create_key_val_offset(
                    bound_offset,
                    bound_offset
                )
            );
        }
    
        node
    }

    /// Get the value slice for the key slice
    pub fn get(&self,key:&[u8])->Option<&[u8]>{
        let idx=self.binary_search(key).ok()?;
        
        Some(self.get_val_slice_at(idx))
    }

    /// Get the mutable value slice for the key slice
    pub fn get_mut(&mut self,key:&[u8])->Option<&mut [u8]>{
        let idx=self.binary_search(key).ok()?;
        
        Some(self.get_val_slice_at_mut(idx))
    }

    pub fn insert(&mut self,key:&[u8],val:&[u8])->Result<Option<Vec<u8>>,OpError>{
        assert!(self.len()<=MAX_PG_ENTRY,"Max entry invariant broken");
        if self.len()==MAX_PG_ENTRY{
            Err(OpError::MaxEntry)
        }
        else if key.len()+val.len()>MAX_ENTRY_SIZE{
            Err(OpError::EntrySizeExceed)
        }
        else if self.space_remain()<key.len()+val.len()+OFFSET_SIZE{
            Err(OpError::OutOfSpace)
        }
        else {
            let (prev_val,idx,shift)=match self.binary_search(key) {
                // Replace val for key
                Ok(idx) => {
                    let cur=Vec::from(self.get_val_slice_at(idx));
                    let size_diff=assert_try_into::<_,i16>(val.len())-assert_try_into::<_,i16>(cur.len());
                    let (_,val_bound)=<(usize,usize)>::assert_try_from(self.key_val_bound());
                    let (_,cur_val_right)=<(usize,usize)>::assert_try_from(self.get_offset_at(idx));
                    let (next_key_right,_)=<(usize,usize)>::assert_try_from(self.get_offset_at(idx+1));
                    // Shift all entries with greater key to 
                    // make space or fill empty space from updated value
                    match size_diff {
                        shift @ ..=-1 => {
                            let right_shift:usize=assert_try_into(shift.checked_abs().unwrap());
                            self.data[val_bound+1..=next_key_right+right_shift].rotate_right(right_shift);
                        },
                        shift @ 1.. => {
                            let left_shift:usize=assert_try_into(shift);
                            self.data[val_bound+1-left_shift..=next_key_right].rotate_left(left_shift);
                        },
                        0=>{}
                    }
                    
                    // Update value
                    self.data[cur_val_right - val.len()+1..=cur_val_right].copy_from_slice(val);

                    (Ok(Some(cur)),idx,size_diff)
                },
                // Insert val and key at offset idx
                Err(idx) => {
                    // For the shifting part, it performs the same logic
                    // as if updating a value with length 0 to be a value that is
                    // key.len() + val.len() and insert the new offset for the new entry
                    let (_,val_bound)=<(usize,usize)>::assert_try_from(
                        self.key_val_bound()
                    );
                    let (next_key_right,next_val_right)=<(usize,usize)>::assert_try_from(self.get_offset_at(idx));
                    let new_key_right=next_key_right;
                    let new_val_right: usize=next_key_right-key.len();
                    let key_val_bytes=[val,key].concat();
                    let mut new_offset=Vec::new();
                    new_offset.write_u32::<Endian>(
                        create_key_val_offset(
                            assert_try_into(new_key_right),
                            assert_try_into(new_val_right)
                        )
                    ).unwrap();
                    
                    // Insert new key/value
                    self.left_shift_and_insert(val_bound+1, next_key_right, &key_val_bytes);
                    
                    // Insert new offset and update length
                    let new_len=self.len()+1;
                    shift_right_and_write(
                        range_buffer_mut::<OffsetBytes>(self.get_offset_slice_mut(), idx, new_len+1),
                        &new_offset
                    );
                    self.set_len(assert_try_into(new_len));

                    (Ok(None),idx,assert_try_into(key_val_bytes.len()))
                }
            };

            // Update key/value offset for larger keys entries after update/insert
            for offset_idx in idx+1..=self.len(){
                let (key_offset,val_offset)=<(i16,i16)>::assert_try_from(
                    self.get_offset_at(offset_idx)
                );
                let new_offset=create_key_val_offset(
                    assert_try_into(key_offset-shift),
                    assert_try_into(val_offset-shift)
                );
                write_u32_with_idx::<Endian>(self.get_offset_slice_mut(), offset_idx, new_offset);
            }

            prev_val
        }
    }

    pub fn iter(&'a self)->EntryRefIter<'a,KC>{
        EntryRefIter::new(self)
    }


    /// Get the flags for the node
    pub fn get_flags(&self)->u16{
        read_u16_with_idx::<Endian>(self.data, 1)
    }
    
    /// Set the flags for the node
    pub fn set_flags(&mut self,flag:u16){
        write_u16_with_idx::<Endian>(self.data, 1, flag);
    }
    
    /// Get number of entries
    pub fn len(&self)->usize{
        read_u16_with_idx::<Endian>(self.data, 1) as usize
    }

    /// Update the length of node on the data page and data structure
    fn set_len(&mut self,len:u16){
        write_u16_with_idx::<Endian>(self.data, 1, len);
    }

    /// Binary search the node for key
    /// Result::Ok is returned with the offset index if found.
    /// Otherwise Result::Err is returned with the offset index where
    /// the new key/val offset should be inserted to maintain order
    fn binary_search(&self,key:&[u8])->Result<usize, usize>{
        OFFSET_INDEX_ARRAY[..self.len() as usize]
        .binary_search_by(
            |i|
            KC::cmp(
                self.get_key_slice_at(*i),
                key
            )
        )
    }

    /// Get the number of bytes remaining
    fn space_remain(&self)->usize{
        if self.len()==0{
            PG_SIZE-META_DATA_SIZE-OFFSET_SIZE
        }
        else {
            // Get the offset at self.len() which does not contain real data
            // and acts as boundry for the true last key/val
            let (next_key_offset,_)=self.key_val_bound();
            let key_val_space_used=PG_SIZE-1-next_key_offset as usize;

            PG_SIZE-META_DATA_SIZE-(self.len()+1)*OFFSET_SIZE-key_val_space_used
        }
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

    /// Return the offset of the byte that bounds the 
    /// last key/val. Or simply the offset that will be used for the 
    /// next key/val.
    fn key_val_bound(&self)->(u16,u16){
        self.get_offset_at(self.len())
    }

    /// Get slice that represents the ith key 
    fn get_key_slice_at(&self,i:usize)->&[u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (key_right,val_right)=self.get_offset_at(i);
        
        &self.data[val_right as usize+1..=key_right as usize]
    }

    /// Get slice that represents the ith value 
    fn get_val_slice_at(&self,i:usize)->&[u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (_,value_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        &self.data[next_key_right as usize + 1 ..= value_right as usize]
    }

    /// Get mutable slice that represents the ith value 
    fn get_val_slice_at_mut(&mut self,i:usize)->&mut [u8]{
        assert!((i)<self.len(),"Out of bound {i}>={}",self.len());
        let (_,value_right)=self.get_offset_at(i);
        let (next_key_right,_)=self.get_offset_at(i+1);

        &mut self.data[next_key_right as usize + 1 ..= value_right as usize]
    }

    /// Get ith key/val offset 
    /// No checks performed so if ith offset is not
    /// properly formated, it is undefined behavior
    fn get_offset_at(&self,i:usize)->(u16,u16){
        get_key_val_offset(
            read_u32_with_idx::<Endian>(self.get_offset_slice(), i)
        )
    }

    /// Get slice that skips metadata and starts at offset
    fn get_offset_slice(&self)->&[u8]{
        &self.data[META_DATA_SIZE..]
    }
    
    /// Get mutable slice that skips metadata and starts at offset
    fn get_offset_slice_mut(&mut self)->&mut [u8]{
        &mut self.data[META_DATA_SIZE..]
    }
}



#[cfg(test)]
mod tests{
    use std::{cmp::Reverse, collections::{BinaryHeap, VecDeque}};

    use self::key_cmp::Lexicological;

    use super::*;


    #[test]
    #[should_panic]
    fn parse_invalid_size(){
        let mut data=vec![0;1000];
        Node::<Lexicological>::parse(data.as_mut_slice());
    }

    #[test]
    fn insert_test1(){
        let mut data=vec![0;PG_SIZE];
        let kv=[("abc",123),("efg",-456)];
        let skv=[("","nothing key"),("something something","string")];
        let mut node:Node<Lexicological>=Node::parse(&mut data);

        for (k,v) in kv{
            let key_bytes=k.as_bytes();
            let val_bytes=<i32>::to_be_bytes(v);
            let old=node.insert(k.as_bytes(), &val_bytes)
            .unwrap();
            assert!(old.is_none(),"{:?}",old);
        }
        
        for (k,v) in skv{
            let key_bytes=k.as_bytes();
            let val_bytes=v.as_bytes();
            let old=node.insert(k.as_bytes(), val_bytes)
            .unwrap();
            assert!(old.is_none(),"{:?}",old);
        }

        let mut iter=node.iter();
        let (k,v)=iter.next().unwrap();
        assert_eq!(k,"".as_bytes());
        assert_eq!(v,"nothing key".as_bytes());

        let (k,v)=iter.next().unwrap();
        assert_eq!(k,"abc".as_bytes());
        assert_eq!(v,&<i32>::to_be_bytes(123));

        let (k,v)=iter.next().unwrap();
        assert_eq!(k,"efg".as_bytes());
        assert_eq!(v,&<i32>::to_be_bytes(-456));

        let (k,v)=iter.next().unwrap();
        assert_eq!(k,"something something".as_bytes());
        assert_eq!(v,"string".as_bytes());

        node.insert("".as_bytes(), "".as_bytes()).unwrap();
        let mut iter=node.iter();
        let (k,v)=iter.next().unwrap();
        assert!(k==Vec::new());
        assert!(v==Vec::new());

    }

    #[test]
    fn insert_test2(){
        let mut data=vec![0;PG_SIZE];
        let mut node:Node<Lexicological>=Node::parse(&mut data);
        for i in 0..(PG_SIZE-META_DATA_SIZE-OFFSET_SIZE)/(OFFSET_SIZE+16){
            node.insert(&i.to_be_bytes(), &i.to_be_bytes()).unwrap();
            assert_ne!("ab".as_bytes(),i.to_be_bytes());
            assert_ne!("abcd".as_bytes(),i.to_be_bytes());
            assert_eq!(node.space_remain(),PG_SIZE-META_DATA_SIZE-OFFSET_SIZE-(i+1)*(OFFSET_SIZE+16));
            assert_eq!(node.len(),i+1);
        }
        assert!(node.insert("abcd".as_bytes(),"abcd".as_bytes()).is_err());
        assert!(node.insert("ab".as_bytes(),"cd".as_bytes()).is_ok());
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
                assert_eq!(String::from_utf8(k.to_vec()).unwrap(),"ab");
                assert_eq!(String::from_utf8(v.to_vec()).unwrap(),"cd");
            }
        }

    }

    #[test]
    fn insert_test3(){
        let mut data=vec![0;PG_SIZE];
        let mut node:Node<Lexicological>=Node::parse(&mut data);
        assert!(node.insert("abc".repeat(1000).as_bytes(), "".as_bytes()).is_err());
        assert_eq!(node.space_remain(),PG_SIZE-META_DATA_SIZE-OFFSET_SIZE);
        assert!(node.insert("abc".repeat(300).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.insert("abc".repeat(300).as_bytes(), "".as_bytes()).unwrap().unwrap(),"".as_bytes());
        assert_eq!(node.len(),1);
        assert!(node.insert("123".repeat(400).as_bytes(), "".as_bytes()).is_ok());
        assert!(node.insert("456".repeat(400).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.len(),3);
        assert!(node.insert("789".repeat(300).as_bytes(), "".as_bytes()).is_err());
        assert!(node.space_remain()<900);
        assert!(node.insert("789".repeat(200).as_bytes(), "".as_bytes()).is_ok());
        assert_eq!(node.len(),4);
        assert!(node.space_remain()<300);
        
        let mut q:VecDeque<usize>=VecDeque::from(vec![1200,1200,600,900]);
        let mut h=BinaryHeap::from(["abc","123","456","789"].map(Reverse));

        for (k,v) in node.iter(){
            assert_eq!(v.len(),0);
            assert_eq!(k.len(),q.pop_front().unwrap());
            assert_eq!(&k[..3],h.pop().unwrap().0.as_bytes());
        }

    }

}