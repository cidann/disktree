use super::{key_cmp::KeyCmp, Node, NodeData};


/// Cursor that points to gaps next to node entries
pub struct Cursor<'a,T,KC>
where
    T:NodeData,
    KC:KeyCmp
{
    node:&'a Node<T,KC>,
    gap_idx:usize
}

impl<'a,T,KC> Cursor<'a,T,KC> 
where
    T:NodeData,
    KC:KeyCmp
{
    /// Create cursor at the given gap index for the given node.
    pub fn new(gap_idx:usize,node:&Node<T,KC>)->Cursor<T,KC>{
        assert!(gap_idx<=node.len());
        Cursor{
           node,
           gap_idx
        }
    }

    /// Move the cursor to the next gap and return the 
    /// entry moved over. If the cursor is already at the
    /// end gap, return None
    pub fn next(&mut self)->Option<(&'a [u8],&'a [u8])>{
        if self.gap_idx==self.node.len(){
            None
        }
        else{
            let res=Some(self.node.get_key_val_slices_at(self.gap_idx));
            self.gap_idx+=1;
            res
        }
    }

    /// Move the cursor to the prev gap and return the 
    /// entry moved over. If the cursor is already at the
    /// start gap, return None.
    pub fn prev(&mut self)->Option<(&'a [u8],&'a [u8])>{
        if self.gap_idx==0{
            None
        }
        else{
            let res=Some(self.node.get_key_val_slices_at(self.gap_idx-1));
            self.gap_idx-=1;
            res
        }
    }

    /// Get the entry after the gap without moving the gap.
    /// If the cursor is at the end gap, return None
    pub fn peek_next(&self)->Option<(&'a [u8],&'a [u8])>{
        if self.gap_idx==self.node.len(){
            None
        }
        else{
            let res=Some(self.node.get_key_val_slices_at(self.gap_idx));
            res
        }
    }

    /// Get the entry before the gap without moving the gap.
    /// If the cursor is at the start gap, return None.
    pub fn peek_prev(&self)->Option<(&'a [u8],&'a [u8])>{
        if self.gap_idx==0{
            None
        }
        else{
            let res=Some(self.node.get_key_val_slices_at(self.gap_idx-1));
            res
        }
    }

}