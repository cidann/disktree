use std::mem::size_of;

use super::{META_DATA_SIZE, OFFSET_SIZE};


pub fn get_key_val_offset(offset:u32)->(u16,u16){
    ((offset>>16).try_into().unwrap(),offset as u16)
}

pub fn create_key_val_offset(key_offset:u16,val_offset:u16)->u32{
    let key_offset:u32=key_offset.into();
    (key_offset<<16).checked_add(val_offset.into()).unwrap()
}

