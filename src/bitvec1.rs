use serde::{Deserialize, Serialize};
use std::convert::TryInto;
use std::marker::PhantomData;
use std::ops::Deref;
use std::fmt::{Debug, Formatter, Result};
use std::ptr;
use std::ptr::{NonNull, Unique};
use std::mem;
use std::alloc::{GlobalAlloc, Layout, Global, handle_alloc_error};
use std::alloc::{alloc, realloc};

use super::iterator::BitIter;
use std::borrow::Borrow;

#[derive(Copy, Clone)]
pub struct BitSliceRef<'a> {
    len: usize,
    slice: &'a [u8],
}

impl<'a> BitSliceRef<'a> {
    pub fn from_slice(slice: &'a[u8], len: usize) -> Self {
        BitSliceRef {
            len,
            slice,
        }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn into_bitbox(self) -> BitBox {
        BitBox {
            len: self.len,
            raw_box: self.slice.into()
        }
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if self.len > index {
            let byte_index = index / 8;
            let bit_index = index % 8;

            let byte = match self.slice.get(byte_index) {
                Some(byte) => byte,
                None => return  None,
            };
            return Some(get_bit_at(*byte, bit_index as u8));
        }
        None
    }

    pub fn iter(self) -> BitIter<'a> {
        BitIter::new(self)
    }
}

#[derive(Clone, Hash, Eq, PartialEq)]
pub struct BitBox {
    len: usize,
    raw_box: Box<[u8]>,
}

impl BitBox {
    pub fn from_box(byte_box: Box<[u8]>, len: usize) -> Self {
        BitBox {
            len,
            raw_box: byte_box,
        }
    }

    pub fn as_bitslice(&self) -> BitSliceRef {
        BitSliceRef {
            len: self.len,
            slice: self.raw_box.as_ref(),
        }
    }
}

#[derive(Clone)]
pub struct BitVec {
    ptr: Unique<u8>,
    len: usize,
    cap: usize,
}

impl BitVec {

    fn grow(&mut self) {
        // this is all pretty delicate, so let's say it's all unsafe
        unsafe {
            // current API requires us to specify size and alignment manually.
            let align = mem::align_of::<u8>();

            let (new_cap, ptr) = if self.cap == 0 {
                let ptr = alloc(Layout::array(1).unwrap());
                (8, ptr)
            } else {
                // as an invariant, we can assume that `self.cap < isize::MAX`,
                // so this doesn't need to be checked.
                let new_cap = self.cap * 2;
                // Similarly this can't overflow due to previously allocating this
                let old_num_bytes = self.cap / 8;

                // check that the new allocation doesn't exceed `isize::MAX` at all
                // regardless of the actual size of the capacity. This combines the
                // `new_cap <= isize::MAX` and `new_num_bytes <= usize::MAX` checks
                // we need to make. We lose the ability to allocate e.g. 2/3rds of
                // the address space with a single Vec of i16's on 32-bit though.
                // Alas, poor Yorick -- I knew him, Horatio.
                assert!(old_num_bytes <= (::std::isize::MAX as usize) / 2,
                        "capacity overflow");

                let new_num_bytes = old_num_bytes * 2;
                let ptr = realloc(self.ptr.as_ptr() as *mut _,
                                           Layout::array(self.cap / 8).unwrap(),
                                           new_num_bytes,
                                         );
                (new_cap, ptr)
            };

            // If allocate or reallocate fail, we'll get `null` back
            if ptr.is_null() { handle_alloc_error(Layout::array(self.cap / 8).unwrap()); }

            self.ptr = Unique::new(ptr as *mut _);
            self.cap = new_cap;
        }
    }

    pub fn new() -> BitVec {
        BitVec {
            ptr: Unique::empty(),
            len: 0,
            cap: 0,
        }
    }

    pub fn pop(&mut self) -> Option<bool> {
        todo!();
        /*if self.len == 0 {
            return None;
        }

        let num = self.bit_in_last_byte();

        if num == 1 {
            let result = get_bit_at(self.ptr.pop().unwrap(), 0);
            self.len -= 1;

            return Some(result);
        } else {
            let result = get_bit_at(*self.ptr.last().unwrap(), num.wrapping_sub(1) as u8);
            self.len -= 1;

            return Some(result);
        }*/
    }

    pub fn push(&mut self, value: bool) {
        todo!()
        /*let num = self.bit_in_last_byte();
        // Check if all byte are full.
        if num == 0 {
            self.ptr.push(0);
            //Unwrap is fine as we just push a value on the vec.
            set_bit_at(self.ptr.last_mut().unwrap(), 0, value)
        } else {
            set_bit_at(self.ptr.last_mut().unwrap(), num as u8, value)
        }

        self.len += 1;*/
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        todo!();
        /*if self.len <= index {
            let byte_index = index / 8;
            let bit_index = index % 8;

            let byte = match self.ptr.get(byte_index) {
                Some(byte) => byte,
                None => return  None,
            };
            return Some(get_bit_at(*byte, bit_index as u8));
        }
        None*/
    }

    pub fn as_bitslice(&self) -> BitSliceRef {
        todo!()
        /*BitSliceRef {
            len: self.len,
            slice: self.ptr.as_slice(),
        }*/
    }

    pub fn extend_from_bitslice(&mut self, slice: BitSliceRef) {
        for bit in slice.iter() {
            self.push(bit)
        }
    }

    pub fn from_vec(vec: Vec<u8>, len: usize) -> Self {
        todo!()
        /*BitVec {
            len,
            ptr
        }*/
    }

    pub fn from_bitbox(bitbox: BitBox) -> Self {
        todo!();
        /*BitVec {
            len: bitbox.len,
            ptr: bitbox.raw_box.into_vec(),
        }*/
    }

    pub fn into_vec(self) -> Vec<u8> {
        todo!()
        //self.ptr
    }

    pub fn into_bitbox(self) -> BitBox {
        todo!()
        /*BitBox {
            len: self.len,
            raw_box: self.ptr.into_boxed_slice(),
        }*/
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        todo!();
        /*
        self.ptr.clear();
        self.len = 0;
        */
    }

    pub fn iter(&self) -> BitIter {
        self.as_bitslice().iter()
    }

    pub fn get_full_bytes(&mut self) -> Vec<u8> {
        todo!()
        /*let num = self.bit_in_last_byte();
        // We only assing a value to plasse the barrow checker.
        let mut remining = 0;

        // If the last bit is not full (the nomber of bit in the
        // BitVec is not equel to mutipole of 8), we extract it.
        if num != 0 {
            remining = self.ptr.pop().unwrap();
        }

        // A vec of all full byte.
        let copy = self.ptr.clone();
        self.ptr.clear();

        if num != 0 {
            // We reinsert the remining bit and set the len to the right value.
            self.ptr.push(remining);
            self.len = num as usize;
        } else {
            self.len = 0;
        }

        copy*/
    }

    pub fn bit_in_last_byte(&self) -> u8 {
        (self.len % 8).try_into().unwrap()
    }
}

impl<'a> PartialEq<BitSliceRef<'a>> for BitSliceRef<'a> {
    fn eq(&self, other: &BitSliceRef) -> bool {
        if self.len == other.len {
            if *self.slice == *other.slice {
                return true;
            }
        }
        return false
    }
}

impl<'a> PartialEq<BitSliceRef<'a>> for BitBox {
    fn eq(&self, other: &BitSliceRef) -> bool {
        self.deref() == other
    }
}

impl<'a> Debug for BitSliceRef<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "BitSliceRef {{ [")?;
        for bit in self.iter() {
            if bit {
                write!(f, "1, ")?;
            }
            else {
                write!(f, "0, ")?;
            }
        }
        write!(f, "] }}")
    }
}

impl Debug for BitBox {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.as_bitslice().fmt(f)
    }
}

impl Debug for BitVec {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        self.as_bitslice().fmt(f)
    }
}

/// Set the bit at position 'n'. Bits are numbred from 0 (most significant) to 7 (least significant).
fn set_bit_at(input: &mut u8, pos: u8, value: bool) {
    assert!(pos < 8);
    *input = *input & (u8::rotate_right(127, pos as u32));

    if value {
        *input = *input | (128 >> pos)
    }
}

/// get the bit at position `n`. Bits are numbered from 0 (most significant) to 7 (least significant).
fn get_bit_at(input: u8, pos: u8) -> bool {
    assert!(pos < 8);
    input & (128 >> pos) != 0
}

mod test {
    #[test]
    fn set_bit_at_15_test() {
        // 255: 11111111
        let mut num = 255;
        for i in 0..4 {
            super::set_bit_at(&mut num, i, false)
        }
        //15: 00001111
        assert_eq!(num, 15);
    }

    #[test]
    fn set_bit_at_255_test() {
        let mut num = 0;
        for i in 0..8 {
            super::set_bit_at(&mut num, i, true);
        }
        // 254: 11111110
        assert_eq!(num, 255)
    }

    #[test]
    fn get_bit_at_127_test() {
        //127: 01111111
        let num = 127;

        let value = super::get_bit_at(num, 0);
        assert!(!value);

        for i in 1..8 {
            let value = super::get_bit_at(num, i);
            assert!(value)
        }
    }

    #[test]
    fn get_bit_at_254_test() {
        //254: 11111110
        let num = 254;
        for i in 0..7 {
            let value = super::get_bit_at(num, i);
            assert!(value)
        }
        let value = super::get_bit_at(num, 7);
        assert!(!value)
    }
}
