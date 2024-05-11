use std::{iter::Rev, ops::{Deref, Index, IndexMut, Sub}, slice::SliceIndex};


pub fn align_to_assert<T,U>(s:&[T])->&[U]{
    let (p,d,s)=unsafe{s.align_to()};
    assert!(p.is_empty()&&s.is_empty());
    d
}


pub fn align_to_mut_assert<T,U>(s:&mut [T])->&mut [U]{
    let (p,d,s)=unsafe{s.align_to_mut()};
    assert!(p.is_empty()&&s.is_empty());
    d
}

pub const fn range_array<const Start:usize,const N:usize>()->[usize;N]{
    let mut arr=[Start;N];
    let mut i=0;
    while i<N {
        arr[i]=Start+i;
        i+=1;
    }
    arr
}


pub fn assert_try_into<T,U>(from:T)->U
where
    T:TryInto<U>
{
    match from.try_into(){
        Ok(v) => v,
        Err(e) => panic!("cast failed"),
    }
}