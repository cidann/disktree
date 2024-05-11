use std::mem::size_of;

use byteorder::ByteOrder;

pub fn get_key_val_offset(offset:u32)->(u16,u16){
    ((offset>>16) as u16,offset as u16)
}

pub fn offset_buffer<T>(buf:&[u8],idx:usize)->&[u8]{
    &buf[idx*size_of::<T>()..]
}

pub fn offset_buffer_mut<T>(buf:&mut [u8],idx:usize)->&mut [u8]{
    &mut buf[idx*size_of::<T>()..]
}


pub fn read_u16_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u16 {
    T::read_u16(offset_buffer::<u16>(buf, idx))
}

pub fn read_u32_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u32 {
    T::read_u32(offset_buffer::<u32>(buf, idx))
}

pub fn read_u64_with_idx<T:ByteOrder>(buf: &[u8], idx: usize) -> u64 {
    T::read_u64(offset_buffer::<u64>(buf, idx))
}

pub fn write_u16_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u16) {
    T::write_u16(offset_buffer_mut::<u16>(buf, idx),val);
}

pub fn write_u32_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u32) {
    T::write_u32(offset_buffer_mut::<u32>(buf, idx),val);
}

pub fn write_u64_with_idx<T:ByteOrder>(buf: &mut [u8], idx: usize, val: u64) {
    T::write_u64(offset_buffer_mut::<u64>(buf, idx),val);
}