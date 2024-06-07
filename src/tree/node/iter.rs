use std::{io::{self, BufRead, Lines}, marker::PhantomData, mem::{self, size_of}, ops::RangeBounds, path::Iter};


use crate::utils::{offset_buffer_mut, range_buffer, range_buffer_mut, read_u32_with_idx, split_buffer_mut};

use super::{key_cmp::KeyCmp, utils::get_key_val_offset, NodeData, MutNodeData, Node, NodeEndian, OffsetBytes};


pub struct EntryRefIter<'a,T,KC>
where
    T:NodeData,
    KC:KeyCmp
{
    idx:usize,
    end:usize,
    node:&'a Node<T,KC>
}

impl<'a,T,KC> EntryRefIter<'a,T,KC> 
where
    T:NodeData,
    KC:KeyCmp
{
    /// Constructs an iterator that yields references to 
    /// slice for key/val over the given range of entry index.
    /// If start and or end is unbounded they are 0 and length 
    /// of node respectively 
    pub fn new<R>(range:R,node:&'a Node<T,KC>)->EntryRefIter<'a,T,KC> 
    where
        R:RangeBounds<usize>
    {
        let start=match range.start_bound() {
            std::ops::Bound::Included(idx) => *idx,
            std::ops::Bound::Excluded(idx) => idx+1,
            std::ops::Bound::Unbounded => 0,
        };
        let end=match range.end_bound() {
            std::ops::Bound::Included(idx) => idx+1,
            std::ops::Bound::Excluded(idx) => *idx,
            std::ops::Bound::Unbounded => node.len(),
        };
        EntryRefIter{
            idx: start,
            end,
            node
        }
    }
}

impl<'a,T,KC> Iterator for EntryRefIter<'a,T,KC> 
where
    T:NodeData,
    KC:KeyCmp
{
    type Item=(&'a[u8],&'a[u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx < self.end{
            let res=Some(self.node.get_key_val_slices_at(self.idx));
            self.idx+=1;
            res
        }
        else{
            None
        }
    }
    
}

pub struct EntryRefIterMut<'a>{
    idx:usize,
    end:usize,
    offset_data:&'a mut [u8],
    kv_data:&'a mut [u8]
}

impl<'a,'b:'a> EntryRefIterMut<'a>{
    /// Constructs an iterator that yields mutable references to 
    /// slice for key/val over the given range of entry index.
    /// If start and or end is unbounded they are 0 and length 
    /// of node respectively 
    pub fn new<R,T,KC>(range:R,node:&'a mut Node<T,KC>)->EntryRefIterMut<'a>
    where
        T:MutNodeData,
        KC:KeyCmp,
        R:RangeBounds<usize>
    {
        let start=match range.start_bound() {
            std::ops::Bound::Included(idx) => *idx,
            std::ops::Bound::Excluded(idx) => idx+1,
            std::ops::Bound::Unbounded => 0,
        };
        let end=match range.end_bound() {
            std::ops::Bound::Included(idx) => idx+1,
            std::ops::Bound::Excluded(idx) => *idx,
            std::ops::Bound::Unbounded => node.len(),
        };
        //Split offset+kv buffer. The resulting offset buffer
        //includes the bounding offset at index node.len()
        let bounding_offset_index=node.len();
        let data_slice=node.skip_metadata_slice_mut();
        let (offset_data,kv_data)=split_buffer_mut::<OffsetBytes>(data_slice, bounding_offset_index+1);


        EntryRefIterMut{
            idx: start,
            end,
            offset_data,
            kv_data
        }
    }
}

impl<'a> Iterator for EntryRefIterMut<'a>{
    type Item=(&'a [u8],&'a mut [u8]);

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx < self.end{
            let (key_right,val_right) = get_key_val_offset(
                read_u32_with_idx::<NodeEndian>(self.offset_data, self.idx)
            );
            let (next_key_right,_) = get_key_val_offset(
                read_u32_with_idx::<NodeEndian>(self.offset_data, self.idx+1)
            );
            let key_size=key_right-val_right;
            let val_size=val_right-next_key_right;
            let remain=mem::take(&mut self.kv_data);
            let (remain,key_slice)=remain.split_at_mut(remain.len()-key_size as usize);
            let (remain,val_slice)=remain.split_at_mut(remain.len()-val_size as usize);
            self.idx+=1;
            self.kv_data=remain;

            Some((key_slice,val_slice))
        }
        else{
            None
        }
    }
   
}

/// Iterator that yields mutable buffer containing
/// Offset to k/v data in node as well as the 
/// bounding offset
pub struct OffsetIterMut<'a>{
    idx:usize,
    end:usize,
    offset_slice:&'a mut [u8]
}

impl<'a> OffsetIterMut<'a> {
    pub fn new<T,KC>(node:&'a mut Node<T,KC>)->OffsetIterMut<'a>
    where
        T:MutNodeData,
        KC:KeyCmp
    {
        let entry_count=node.len();
        Self::from_buffer(node.skip_metadata_slice_mut(), entry_count)
    }

    fn from_buffer(buf:&'a mut [u8],len:usize)->OffsetIterMut<'a>{
        OffsetIterMut{
            idx:0,
            end:len+1,
            offset_slice:buf
        }
    }
}

impl<'a> Iterator for OffsetIterMut<'a>{
    type Item=&'a mut [u8];

    fn next(&mut self) -> Option<Self::Item> {
        if self.idx<self.end{
            let offset_slice=mem::take(&mut self.offset_slice);
            self.offset_slice=<&mut [u8]>::default();
            let (offset,remain)=split_buffer_mut::<OffsetBytes>(offset_slice, 1);
            debug_assert_eq!(offset.len(),size_of::<OffsetBytes>());
            self.idx+=1;
            self.offset_slice=remain;

            Some(offset)
        }
        else {
            None
        }
    }

    fn nth(&mut self, n: usize) -> Option<Self::Item> {
        self.idx+=n;
        self.offset_slice=offset_buffer_mut::<OffsetBytes>(mem::take(&mut self.offset_slice), n);
        self.next()
    }
}

