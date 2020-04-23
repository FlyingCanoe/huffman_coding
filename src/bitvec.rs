use serde::{Deserialize, Serialize};
use std::alloc::{alloc, realloc, dealloc};
use std::alloc::{handle_alloc_error, Global, GlobalAlloc, Layout};
use std::convert::TryInto;
use std::fmt::{Debug, Formatter, Result};
use std::marker::PhantomData;
use std::mem;
use std::ops::Deref;
use std::ptr;
use std::ptr::{NonNull, Unique};
use std::slice;

use super::iterator::BitIter;
use std::borrow::Borrow;
use std::hash::{Hash, Hasher};

#[derive(Copy, Clone, Eq, PartialEq, Hash)]
pub struct BitSliceRef<'a> {
    len: usize,
    slice: &'a [u8],
}

impl<'a> BitSliceRef<'a> {
    pub fn from_slice(slice: &'a [u8], len: usize) -> Self {
        assert!(slice.len() >= len / 8);
        BitSliceRef { len, slice }
    }

    pub fn len(&self) -> usize {
        self.len
    }

    fn to_box(self) -> Box<[u8]> {
        self.slice.into()
    }

    pub fn into_bitbox(self) -> BitBox {
        let temp_box = self.slice.into();
        BitBox::from_box(temp_box, self.len)
    }

    pub fn get(&self, index: usize) -> Option<bool> {
        if self.len > index {
            let byte_index = index / 8;
            let bit_index = index % 8;

            let byte = match self.slice.get(byte_index) {
                Some(byte) => byte,
                None => return None,
            };
            return Some(get_bit_at(*byte, bit_index as u8));
        }
        None
    }

    pub fn iter(self) -> BitIter<'a> {
        BitIter::new(self)
    }
}

pub struct BitBox {
    len: usize,
    ptr: Unique<u8>,
}

#[derive(Clone, Serialize, Deserialize)]
pub struct BadBitBox {
    len: usize,
    ptr: Box<[u8]>
}

impl BadBitBox {
    pub(crate) fn into_bit_box(self) -> BitBox {
        BitBox::from_box(self.ptr, self.len)
    }
}

impl BitBox {
    pub(crate) fn into_bad_bit_box(self) -> BadBitBox {
        BadBitBox {
            len: self.len,
            ptr: self.as_bitslice().to_box()
        }
    }

    pub fn from_box(mut byte_box: Box<[u8]>, len: usize) -> Self {
        BitBox {
            len,
            ptr: Unique::new(Box::into_raw(byte_box) as *mut u8).unwrap(),
        }
    }

    pub fn as_bitslice(&self) -> BitSliceRef {
        BitSliceRef {
            len: self.len,
            slice: unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.byte_len()) },
        }
    }

    fn byte_len(&self) -> usize {
        if self.len % 8 == 0 {
            self.len / 8
        }
        else {
            self.len / 8 + 1
        }
    }
}

//#[derive(Clone)]
pub struct BitVec {
    len: usize,
    cap: usize,
    ptr: Unique<u8>,
}

impl BitVec {
    fn grow(&mut self) {
        unsafe {
            let (new_cap, ptr) = if self.cap == 0 {
                let ptr = alloc(Layout::array::<u8>(1).unwrap());
                (8, ptr)
            } else {
                let new_cap = self.cap.checked_mul(2).unwrap();
                let old_num_bytes = self.byte_cap();

                // this cant overflow because a bitvec can only contain usize bit thus
                // usize / 8 byte.
                let new_num_bytes = old_num_bytes * 2;
                let ptr = realloc(
                    self.ptr.as_ptr(),
                    Layout::array::<u8>(new_num_bytes).unwrap(),
                    new_num_bytes,
                );
                (new_cap, ptr)
            };

            // If allocate or reallocate fail, we'll get `null` back
            if ptr.is_null() {
                handle_alloc_error(Layout::array::<u8>(self.byte_cap()).unwrap());
            }

            self.ptr = Unique::new(ptr).unwrap();
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
        if self.len == 0 {
            return None
        }
        let results = self.get(self.len -1 );
        self.len -= 1;

        return results
    }

    fn pop_byte(&mut self) -> Option<u8> {
        let byte_len = self.byte_len();
        if byte_len == 0 {
            return None
        }

        let byte = unsafe { self.ptr.as_ptr().offset((byte_len - 1) as isize).read() };
        let num = self.bit_in_last_byte();

        if num == 0 {
            self.len -= 8;
        }
        else {
            self.len -= num as usize;
        }
        Some(byte)
    }

    pub fn push(&mut self, value: bool) {
        if self.len == self.cap {
            self.grow()
        }


        // check if all byte are full
        if self.len % 8 == 0 {
            unsafe {
                if value {
                    ptr::write(
                        self.ptr.as_ptr().offset(self.byte_len() as isize),
                        0b10_00_00_00,
                    )
                } else {
                    ptr::write(self.ptr.as_ptr().offset(self.byte_len() as isize), 0)
                }
            }
        } else {
            let bit_offset = self.bit_in_last_byte();
            let last_byte = unsafe { &mut * self.ptr.as_ptr().offset((self.byte_len().saturating_sub(1)) as isize) };

            set_bit_at(last_byte, bit_offset, value);
        }

        self.len += 1;
    }

    fn push_byte(&mut self, byte: u8) {

    }

    fn get(&self, index: usize) -> Option<bool> {

        if self.len > index {
            let byte_index = index / 8;
            let bit_index = index % 8;

            let byte = unsafe { self.ptr.as_ptr().offset(byte_index as isize).read() };

            return Some(get_bit_at(byte, bit_index as u8))
        }
        None
    }


    pub fn as_bitslice(&self) -> BitSliceRef {
        BitSliceRef {
            len: self.len,
            slice: unsafe { slice::from_raw_parts(self.ptr.as_ptr(), self.byte_len()) },
        }
    }

    pub fn extend_from_bitslice(&mut self, slice: BitSliceRef) {
        for bit in slice.iter() {
            self.push(bit)
        }
    }

    /// crate a bitvec from a Vec<u8>
    /// #Panic
    /// a bitvec can only hold usize::MAX bit. If you give this function a vec<u8> with more than
    /// usize:max / 8 element it will panic
    pub fn from_vec(vec: Vec<u8>) -> Self {
        let (ptr ,mut len, mut cap) = vec.into_raw_parts();
        len = len.checked_mul(8).unwrap();
        cap = cap.checked_mul(8).unwrap();
        let ptr = Unique::new(ptr).unwrap();

        BitVec {
            len,
            cap,
            ptr,
        }
    }

    pub fn from_bitbox(bitbox: BitBox) -> Self {
        todo!();
        /*BitVec {
            len: bitbox.len,
            ptr: bitbox.raw_box.into_vec(),
        }*/
    }

    pub fn into_vec(self) -> Vec<u8> {
        unsafe {
            let vec = Vec::from_raw_parts(
                self.ptr.as_ptr(),
                self.byte_len(),
                self.byte_cap(),
            );
            mem::forget(self);
            vec
        }
    }

    pub fn into_bitbox(self) -> BitBox {
        let r = BitBox {
            len: self.len,
            ptr: Unique::new(self.ptr.as_ptr()).unwrap(),
        };

        mem::forget(self);
        r
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn clear(&mut self) {
        self.len = 0
    }

    pub fn iter(&self) -> BitIter {
        self.as_bitslice().iter()
    }

    pub fn get_full_bytes(&mut self) -> Vec<u8> {
        let num = self.bit_in_last_byte();
        //let mut reminige;

        if num == 0 {
            let output_vec = self.clone().into_vec();
            self.clear();
            output_vec
        }
        else {
            let byte = self.pop_byte().unwrap();
            let output_vec = self.clone().into_vec();
            self.clear(); unsafe {
                *self.ptr.as_mut() = byte;
            }
            self.len = num as usize;
            output_vec
        }
    }

    /// return the number of bytes the BitVec is using
    fn byte_len(&self) -> usize {
        if self.len % 8 == 0 {
            self.len / 8
        }
        else {
            self.len / 8 + 1
        }
    }

    /// return the number of bytes the BitVec have allocate
    fn byte_cap(&self) -> usize {
        self.cap / 8
    }

    pub fn bit_in_last_byte(&self) -> u8 {
        (self.len % 8).try_into().unwrap()
    }
}

impl<'a> PartialEq<BitSliceRef<'a>> for BitBox {
    fn eq(&self, other: &BitSliceRef) -> bool {
        self.as_bitslice() == *other
    }
}

impl PartialEq<BitBox> for BitBox {
    fn eq(&self, other: &BitBox) -> bool {
        self.eq(&other.as_bitslice())
    }
}

impl Eq for BitBox {}

impl Clone for BitVec {
    fn clone(&self) -> Self {
        unsafe {
            if self.len != 0 {
                let ptr = alloc(Layout::array::<u8>(self.byte_cap()).unwrap());
                ptr::copy_nonoverlapping(self.ptr.as_ptr(), ptr, self.byte_len());
                BitVec {
                    len: self.len,
                    cap: self.cap,
                    ptr: Unique::new(ptr).unwrap(),
                }
            }
            else {
                BitVec::new()
            }
        }
    }
}

impl Clone for BitBox {
    fn clone(&self) -> Self {
        unsafe {
            if self.len != 0 {
                let ptr = alloc(Layout::array::<u8>(self.byte_len()).unwrap());
                ptr::copy_nonoverlapping(self.ptr.as_ptr(), ptr, self.byte_len());
                BitBox {
                    len: self.len,
                    ptr: Unique::new(ptr).unwrap(),
                }
            }
            else {
                panic!()
            }
        }
    }
}

impl<'a> Debug for BitSliceRef<'a> {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result {
        write!(f, "BitSliceRef {{ [")?;
        for bit in self.iter() {
            if bit {
                write!(f, "1, ")?;
            } else {
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

impl Hash for BitBox {
    fn hash<H: Hasher>(&self, state: &mut H) {
        self.as_bitslice().hash(state)
    }
}

impl Drop for BitBox {
    fn drop(&mut self) {
        let num_bytes = self.byte_len();

        if num_bytes != 0 {
            unsafe {
                dealloc(self.ptr.as_ptr(), Layout::array::<u8>(num_bytes).unwrap())
            }
        }
    }
}

impl Drop for BitVec {
    fn drop(&mut self) {
        let num_bytes = self.byte_cap();
        assert_eq!(1, mem::align_of::<u8>());
        assert_eq!(1, mem::size_of::<u8>());

        if num_bytes != 0 {
            //while let Some(_) = self.pop() { }
            unsafe {
                dealloc(self.ptr.as_ptr(), Layout::array::<u8>(self.byte_cap()).unwrap())
            }
        }
    }
}

/// Set the bit at position 'n'. Bits are numbered from 0 (most significant) to 7 (least significant).
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
    use super::BitVec;
    use std::ptr::Unique;
    use crate::bitvec::get_bit_at;
    use std::ptr::NonNull;

    struct foo {
        len: usize,
        cap: usize,
        ptr: Unique<u8>,
    }

    #[test]
    fn pop_empty_bitvec() {
        let mut vec = BitVec::new();
        assert_eq!(vec.pop(), None);
    }

    #[test]
    fn pop_bitvec() {
        let mut vec = BitVec::new();
        vec.push(false);
        vec.push(true);

        assert_eq!(vec.pop(), Some(true));
        assert_eq!(vec.pop(), Some(false));
        assert_eq!(vec.pop(), None);
    }

    #[test]
    fn new_bitvec() {
        let vec = BitVec::new();
        assert_eq!(vec.len, 0);
        assert_eq!(vec.cap, 0);
    }

    #[test]
    fn grow_bitvec() {
        let mut vec = BitVec::from_vec(vec![0, 0]);
        assert_eq!(vec.len, 16);
        assert_eq!(vec.cap, 16);
        vec.grow();

        assert_eq!(vec.cap, 32);
    }


    #[test]
    fn grow_bitvec_empty()  {
        let mut vec = BitVec::new();
        assert_eq!(vec.cap, 0);
        vec.grow();

        assert_eq!(vec.cap, 8);
        assert_eq!(vec.len, 0);
    }
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
    fn get_bit_at_64() {
        let num = 64;
        let mut boolvec = vec![];

        for i in 0..8 {
            let temp = get_bit_at(num, i);
            boolvec.push(temp);
        }

        assert_eq!(boolvec, vec![false, true, false, false, false, false, false, false])
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
