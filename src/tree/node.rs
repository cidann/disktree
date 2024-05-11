use std::{ collections::btree_map::Keys, marker::PhantomData, mem::{size_of, size_of_val}, ops::Shl, process::id};
use core::array;
use byteorder::{BigEndian, ByteOrder};

use crate::{tree::node::utils::{get_key_val_offset, read_u32_with_idx}, utils::{align_to_assert, align_to_mut_assert, assert_try_into, range_array}};

mod utils;


/*
//////////////////////////////////////////////////////////////////////////////////////////
/ flags | len | (key_start_offset1,val_end_offset1),(key_start_offset2,val_end_offset2), /
/ (key_start_offset3,val_end_offset3),...,(last_key_end,last_val_end) | key1,key2,key3,. /
/ ..                                                                                     /
/                                                                                        /
/                                                                     ...,val3,val2,val1 /
//////////////////////////////////////////////////////////////////////////////////////////
*/

const PG_SIZE:usize=4096;
const PG_HEADER_SIZE:usize=1024;
const META_DATA_SIZE:usize=size_of::<MetaDataBytes>();
const OFFSET_SIZE:usize=size_of::<KeyValOffsetBytes>();
const OFFSET_ARRAY_SIZE:usize=PG_HEADER_SIZE-META_DATA_SIZE;
const MAX_PG_ENTRY:usize=(OFFSET_ARRAY_SIZE)/OFFSET_SIZE-1;

const OFFSET_INDEX_ARRAY:[usize;MAX_PG_ENTRY]=range_array::<0,MAX_PG_ENTRY>();


type Endian=BigEndian;

pub type MetaDataBytes=u32;
pub type KeyValOffsetBytes=u32;
pub type OffsetBytes=u16;



/// Zero Copy Node holding slice of page data
/// The keys and values are expected to be encrypted into byte slices
/// which will be compared lexicologically when needed
/// All data is stored in big endian order
struct Node<'a>{
    flags:u16,
    len:u16,
    data:&'a mut [u8],
}

impl<'a> Node<'a> {
    ///parse a page of PG_SIZE bytes into a node in place. 
    /// #Safety
    /// This function panics if the slice is not exactly PG_SIZE
    pub fn parse(data:&'a mut [u8])->Node{
        assert_eq!(data.len(),PG_SIZE,"Expected data size {} to match page size {}",data.len(),PG_SIZE);
        let flags:u16=(data[0] as u16).shl(8)+data[1] as u16;
        let len:u16=(data[2] as u16).shl(8)+data[3] as u16;
        assert!(len as usize<=MAX_PG_ENTRY,"Number of entries {} exceeded limit {}",len,MAX_PG_ENTRY);
        
        Node{
            flags,
            len,
            data,
        }
    }

    ///Get the value slice for the key slice
    pub fn get(&self,key:&[u8])->Option<&[u8]>{
        let idx=OFFSET_INDEX_ARRAY[..self.len as usize]
        .binary_search_by_key(&key, |i|self.get_key_slice_at(assert_try_into(*i)))
        .ok()?;
        
        Some(self.get_val_slice_at(assert_try_into(idx)))
    }

    ///Get the mutable value slice for the key slice
    pub fn get_mut(&mut self,key:&[u8])->Option<&mut [u8]>{
        let idx=OFFSET_INDEX_ARRAY[..self.len as usize]
        .binary_search_by_key(&key, |i|self.get_key_slice_at(assert_try_into(*i)))
        .ok()?;
        
        Some(self.get_val_slice_at_mut(assert_try_into(idx)))
    }

    ///Get the flags slice for the node
    pub fn get_flags(&self)->&u16{
        &self.flags
    }
    
    ///Get the mutable flags slice for the node
    pub fn get_flags_mut(&mut self)->&mut u16{
        &mut self.flags
    }

    ///Get slice that represents the ith key 
    fn get_key_slice_at(&self,i:u16)->&[u8]{
        assert!(i<self.len,"Out of bound {i}>={}",self.len);
        let offset_slice=self.get_offset_slice();
        let (key_start_offset,_)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, i.into()));
        let (key_end,_)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, (i+1).into()));

        &self.data[key_start_offset as usize..key_end as usize]
    }

    ///Get mutable slice that represents the ith key 
    fn get_key_slice_at_mut(&mut self,i:u16)->&mut [u8]{
        assert!(i<self.len,"Out of bound {i}>={}",self.len);
        let offset_slice=self.get_offset_slice();
        let (key_start_offset,_)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, i.into()));
        let (key_end,_)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, (i+1).into()));

        &mut self.data[key_start_offset as usize..key_end as usize]
    }

    ///Get slice that represents the ith value 
    fn get_val_slice_at(&self,i:u16)->&[u8]{
        assert!(i<self.len,"Out of bound {i}>={}",self.len);
        let offset_slice=self.get_offset_slice();
        let (_,value_offset)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, i.into()));
        let (_,value_end)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, (i+1).into()));

        &self.data[value_end as usize + 1 ..= value_offset as usize]
    }

    ///Get mutable slice that represents the ith value 
    fn get_val_slice_at_mut(&mut self,i:u16)->&mut [u8]{
        assert!(i<self.len,"Out of bound {i}>={}",self.len);
        let offset_slice=self.get_offset_slice();
        let (_,value_offset)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, i.into()));
        let (_,value_end)=get_key_val_offset(read_u32_with_idx::<Endian>(offset_slice, (i+1).into()));

        &mut self.data[value_end as usize + 1 ..= value_offset as usize]
    }

    ///Get slice that contains offset portion of page
    fn get_offset_slice(&self)->&[u8]{
        &self.data[META_DATA_SIZE..]
    }
    ///Get mutable slice that contains offset portion of page
    fn get_offset_slice_mut(&mut self)->&mut [u8]{
        &mut self.data[META_DATA_SIZE..]
    }

    ///Get slice that contain key/value portion of page
    fn get_key_val_slice(&self)->&[u8]{
        &self.data[PG_HEADER_SIZE..]
    }
    ///Get mutable slice that contain key/value portion of page
    fn get_key_val_slice_mut(&mut self)->&mut [u8]{
        &mut self.data[PG_HEADER_SIZE..]
    }
}



#[cfg(test)]
mod tests{
    use super::*;


    #[test]
    #[should_panic]
    fn parse_invalid_size(){
        let mut data=vec![0;1000];
        Node::parse(data.as_mut_slice());
    }

    #[test]
    fn data_format1(){
        let mut data=vec![0;PG_SIZE];
        //Last pair ("",0) is used as placeholder so that previous key/val 
        //will have end/start boundry
        let kv:Vec<(_,i32)>=vec![("abc",123),("efg",-456),("",0)];
        data[3]=2;
        let mut prev_key_len=0;
        let mut prev_val_len=0;
        for (i,(k,v)) in kv.iter().enumerate(){
            let key_bytes=k.as_bytes();
            let val_bytes=v.to_be_bytes();
            

            data[PG_HEADER_SIZE+prev_key_len..PG_HEADER_SIZE+prev_key_len+key_bytes.len()].copy_from_slice(key_bytes);
            data[PG_SIZE-prev_val_len-size_of_val(v)..PG_SIZE-prev_val_len].copy_from_slice(&val_bytes);
            data[META_DATA_SIZE+4*i..META_DATA_SIZE+4*i+2].copy_from_slice(&((PG_HEADER_SIZE+prev_key_len)as u16).to_be_bytes());
            data[META_DATA_SIZE+4*i+2..META_DATA_SIZE+4*i+4].copy_from_slice(&((PG_SIZE-1-prev_val_len)as u16).to_be_bytes());

            prev_key_len+=key_bytes.len();
            prev_val_len+=val_bytes.len();
        }

        let node=Node::parse(data.as_mut_slice());

        let abc=node.get("abc".as_bytes()).unwrap();
        let efg=node.get("efg".as_bytes()).unwrap();
        assert!(node.get("not".as_bytes()).is_none(),"Did not expect key to be in node");
        assert_eq!(i32::from_be_bytes(abc.try_into().unwrap()),123);
        assert_eq!(i32::from_be_bytes(efg.try_into().unwrap()),-456);
        assert_eq!(node.len,2);
    }
}