use std::{borrow::Borrow, cmp::Ordering, collections::HashSet, fmt::Debug, iter::Rev, mem::size_of, ops::{Deref, Index, IndexMut, Range, RangeBounds, Sub}, process::abort, result, slice::SliceIndex};
use byteorder::ByteOrder;
use rand::{distributions::Alphanumeric, thread_rng, Rng};

use proptest::{prelude::prop, prop_compose, strategy::{Just, Strategy}};

/// Create a compile time array of range [START..START+N-1]s
pub const fn range_array<const START:usize,const N:usize>()->[usize;N]{
    let mut arr=[START;N];
    let mut i=0;
    while i<N {
        arr[i]=START+i;
        i+=1;
    }
    arr
}

/// Shift the buffer left data.len() bytes and write the data
/// in the right most data.len() bytes
/// The left most data.len() bytes are discarded
/// #Panics
/// panics if data.len()>buf.len()
pub fn shift_left_and_write(buf:&mut [u8],data:&[u8]){
    let buf_len=buf.len();
    buf.rotate_left(data.len());
    buf[buf_len-data.len()..].copy_from_slice(data);
}

/// Shift the buffer right data.len() bytes and write the data
/// in the left most data.len() bytes
/// The right most data.len() bytes are discarded
/// #Panics
/// panics if data.len()>buf.len()
pub fn shift_right_and_write(buf:&mut [u8],data:&[u8]){

    buf.rotate_right(data.len());
    buf[..data.len()].copy_from_slice(data);
}


/// offset the buffer to start at idx as if each element is T
pub fn offset_buffer<T>(buf:&[u8],idx:usize)->&[u8]{
    &buf[idx*size_of::<T>()..]
}

/// offset the mutable buffer to start at idx as if each element is T
pub fn offset_buffer_mut<T>(buf:&mut [u8],idx:usize)->&mut [u8]{
    &mut buf[idx*size_of::<T>()..]
}


/// return range of buffer [start..end) as if each item is size of T
pub fn range_buffer<T>(buf:&[u8],start:usize,end:usize)->&[u8]{
    &buf[start*size_of::<T>()..end*size_of::<T>()]
}

/// return range of mutable buffer [start..end) as if each item is size of T
pub fn range_buffer_mut<T>(buf:&mut [u8],start:usize,end:usize)->&mut [u8]{
    &mut buf[start*size_of::<T>()..end*size_of::<T>()]
}

/// Split the buffer such that the first half contain [0,idx) 
/// and second half have [idx,len) where each index refer 
/// to item of size_of::<T> size
pub fn split_buffer<T>(buf:&[u8],idx:usize)->(&[u8],&[u8]){
    buf.split_at(size_of::<T>()*idx)
}

/// Split the mutable buffer such that the first half contain [0,idx) 
/// and second half have [idx,len) where each index refer 
/// to item of size_of::<T> size
pub fn split_buffer_mut<T>(buf:&mut [u8],idx:usize)->(&mut [u8],&mut [u8]){
    buf.split_at_mut(size_of::<T>()*idx)
}


/// Read the idx element of u16 size with T byte order
pub fn read_u16_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u16 {
    T::read_u16(offset_buffer::<u16>(buf, idx))
}

/// Read the idx element of u32 size with T byte order
pub fn read_u32_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u32 {
    T::read_u32(offset_buffer::<u32>(buf, idx))
}

/// Read the idx element of u64 size with T byte order
pub fn read_u64_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u64 {
    T::read_u64(offset_buffer::<u64>(buf, idx))
}

/// write val to the idx element of u16 size with T byte order
pub fn write_u16_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u16) {
    T::write_u16(offset_buffer_mut::<u16>(buf, idx),val);
}

/// write val to the idx element of u32 size with T byte order
pub fn write_u32_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u32) {
    T::write_u32(offset_buffer_mut::<u32>(buf, idx),val);
}

/// write val to the idx element of u64 size with T byte order
pub fn write_u64_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u64) {
    T::write_u64(offset_buffer_mut::<u64>(buf, idx),val);
}

/// Generate a random string with length within len_range
pub fn generate_string(len_range:Range<usize>)->String{
    let mut rng=thread_rng();
    let len=rng.gen_range(len_range);
    rng
    .sample_iter(&Alphanumeric)
    .take(len)
    .map(char::from)
    .collect()
}

/// Generate a set of unique indexes within the range
pub fn generate_indexex(range:Range<usize>)->HashSet<usize>{
    let mut indexes=HashSet::new();
    let mut rng=thread_rng();
    while indexes.len()<(range.end-range.start)/2 {
        indexes.insert(rng.gen_range(range.clone()));
    };

    indexes
}

pub fn generate_kv_strategy(kv_len:usize,entries:usize)->impl Strategy<Value = (Vec<(String,String)>,Vec<usize>,Vec<usize>,Vec<(String,String)>)>{
    let kv_strat=format!(".{{1,{kv_len}}}");
    let key_strat=prop::string::string_regex(&kv_strat).unwrap();
    let val_strat=prop::string::string_regex(&kv_strat).unwrap();
    let input_pairs=prop::collection::vec((key_strat,val_strat), entries/2..=entries);
    input_pairs.prop_flat_map(|input_pairs|{
        (
            prop::collection::vec(0..input_pairs.len(), 0..input_pairs.len()),
            prop::collection::vec(0..input_pairs.len(), 0..input_pairs.len()),
            prop::collection::vec(generate_string_range_strategy(), 0..input_pairs.len()),
            Just(input_pairs),
        )
    })
    .prop_map(|(get,remove,range,input)|{
        (input,get,remove,range)
    })
}


//Generate pair of string (s1,s2) where s1<=s2 
pub fn generate_string_range_strategy()->impl Strategy<Value = (String,String)>{
    (".{0,20}",".{0,20}")
    .prop_map(|(first,second)|{
        match first.cmp(&second){
            Ordering::Less => {
                (first,second)
            },
            Ordering::Equal => {
                (first,second)
            },
            Ordering::Greater => {
                (second,first)
            },
        }
    })
}


/// try_into cast that panics if cast fails
pub fn assert_try_into<T,U>(from:T)->U
where
    T:TryInto<U>,
{
    match from.try_into(){
        Ok(v) => v,
        Err(e) => panic!("failed to cast"),
    }
}

/// try_from and assert for tuples since std 
/// does not implement from between tuples that 
/// have all element implementing from
pub trait TupleAssertTryFrom<T>: Sized {
    fn assert_try_from(from: T) -> Self;
}


impl<T0, U0> TupleAssertTryFrom<(T0,)> for (U0,)
where
    U0: TryFrom<T0>,
{
    fn assert_try_from((from,): (T0,)) -> Self {
        (assert_try_into(from),)
    }
}

impl<T0, T1, U0, U1> TupleAssertTryFrom<(T0, T1)> for (U0, U1)
where
    U0: TryFrom<T0>,
    U1: TryFrom<T1>,
{
    fn assert_try_from((from0, from1): (T0, T1)) -> Self {
        (assert_try_into(from0), assert_try_into(from1))
    }
}

impl<T0, T1, T2, U0, U1, U2> TupleAssertTryFrom<(T0, T1, T2)> for (U0, U1, U2)
where
    U0: TryFrom<T0>,
    U1: TryFrom<T1>,
    U2: TryFrom<T2>,
{
    fn assert_try_from((from0, from1, from2): (T0, T1, T2)) -> Self {
        (
            assert_try_into(from0),
            assert_try_into(from1),
            assert_try_into(from2),
        )
    }
}

impl<T0, T1, T2, T3, U0, U1, U2, U3> TupleAssertTryFrom<(T0, T1, T2, T3)> for (U0, U1, U2, U3)
where
    U0: TryFrom<T0>,
    U1: TryFrom<T1>,
    U2: TryFrom<T2>,
    U3: TryFrom<T3>,
{
    fn assert_try_from((from0, from1, from2, from3): (T0, T1, T2, T3)) -> Self {
        (
            assert_try_into(from0),
            assert_try_into(from1),
            assert_try_into(from2),
            assert_try_into(from3),
        )
    }
}
