
use core::panic;
use std::{cmp::Reverse, collections::{BTreeMap, BinaryHeap, VecDeque}, iter::{repeat, repeat_with}, mem::size_of};

use crate::{tree::node::{key_cmp::Lexicological, Node, OffsetBytes, META_DATA_SIZE, OFFSET_SIZE}, utils::{generate_indexex, generate_string}};

use super::super::*;

use rand::{seq::SliceRandom, thread_rng};

#[test]
fn insert_test1(){
    let mut data=vec![0;4096];
    let kv=[("abc",123),("efg",-456)];
    let skv=[("","nothing key"),("something something","string")];
    let mut node:Node<&mut [u8],Lexicological>=Node::new(&mut data);

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


    assert_eq!(node.get("abc".as_bytes()).unwrap(),&(123i32.to_be_bytes()));
    assert_eq!(node.get("".as_bytes()).unwrap(),"".as_bytes());
    assert_eq!(node.get("something something".as_bytes()).unwrap(),"string".as_bytes());
    assert_eq!(node.get("efg".as_bytes()).unwrap(),&((-456i32).to_be_bytes()));
    
    assert_eq!(node.get("abce".as_bytes()),None);
}

#[test]
fn insert_test4(){
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


    for (k,v) in node.iter(){
        let (heap_k,heap_v)=inputs.pop_first().unwrap();
        assert_eq!((k,v),(heap_k.as_bytes(),heap_v.as_bytes()))
    }

    let mut keys=inputs.keys().collect::<Vec<_>>();
    keys.shuffle(&mut thread_rng());

    for k in keys{
        assert_eq!(inputs.get(k).unwrap().as_bytes(),node.get(k.as_bytes()).unwrap());
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
