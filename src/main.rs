use std::sync::{Mutex, MutexGuard};

trait AT{
    type B:BT;
    fn get(&mut self)->Self::B;
}

trait BT{
    type C<'a>:CT<'a> where Self:'a;
    fn get<'a,'b:'a>(&'b mut self)->Self::C<'a>;
    fn shorten<'a,'b:'a>(c:Self::C<'b>)->Self::C<'a>;
}

trait CT<'a>{
    fn get(&mut self)->&mut i32;
}

struct A{}
struct B{data:i32}
struct C<'a>{data:&'a mut B}

impl AT for A {
    type B=B;

    fn get(&mut self)->Self::B {
        B{data:0}
    }
}

impl BT for B {
    type C<'a>=C<'a>;

    fn get<'a,'b:'a>(&'b mut self)->Self::C<'a>{
        C{data:self}
    }

    fn shorten<'a,'b:'a>(c:Self::C<'b>)->Self::C<'a>{
        c
    }
}

impl<'a> CT<'a> for C<'a> {
    fn get(& mut self)->& mut i32{
        &mut self.data.data
    }
}

fn test<T:BT>(b:&mut T){
    let mut c=b.get();
    let data=c.get();
}

fn recursion1<'a,T:AT>(a:&mut T,v:Vec<<T::B as BT>::C<'a>>){
    let mut b=a.get();
    let mut c=b.get();
    let mut v:Vec<_>=v.into_iter().map(T::B::shorten).collect();

    v.push(c);

    if v.len()<10{
        recursion1(a, v);
    }
}

fn recursion2<'a,T:AT>(a:&mut T,v:Vec<& T::B>){
    let b=a.get();
    let mut v=v;

    v.push(&b);

    if v.len()<10{
        recursion2(a, v);
    }
}



fn recursion3(v:Vec<&mut i32>){
    let mut i=0;
    let ir=&mut i;
    let mut v=v;

    v.push(ir);

    if v.len()<10{
        recursion3(v);
    }
}


// trait Test{
//     fn get<'a>(&'a mut self)->&'a mut i32;
// }

// struct TestStruct{
//     data:i32
// }

// impl Test for TestStruct {
//     fn get<'a>(&'a mut self)->&'a mut i32 {
//         &mut self.data
//     }
// }

// fn test<T:Test>(a:T){
//     let mut a=a;
//     let data=a.get();
// }




fn main(){
}