#![feature(ptr_internals)]
#![feature(allocator_api)]
#![feature(alloc_layout_extra)]
#![feature(vec_into_raw_parts)]
#![feature(try_blocks)]

//use bitvec::prelude::*;
use std::cmp::Ordering;
use std::collections::binary_heap::BinaryHeap;
use std::collections::BTreeMap;
use std::collections::HashMap;
use std::io;

pub mod bitvec;
use bitvec::{BitBox, BitSliceRef, BitVec, BadBitBox};

mod iterator;
use iterator::{Bits, CharOrRaw, CharsOrRaws};

use anyhow;
use anyhow::bail;
use anyhow::Context;
use rustc_hash::FxHashMap;
use serde::export::Option::Some;

const END_OF_FILE: [u8; 5] = [0, 0, 0, 0, 0];

#[derive(Clone, Eq, PartialEq, Debug)]
enum NodeKind {
    Internal(Box<Node>, Box<Node>),
    Leaf(CharOrRaw),
}

#[derive(Clone, Eq, PartialEq, Debug)]
struct Node {
    frequency: usize,
    kind: NodeKind,
}

impl Ord for Node {
    fn cmp(&self, rhs: &Self) -> std::cmp::Ordering {
        rhs.frequency.cmp(&self.frequency)
    }
}

impl PartialOrd for Node {
    fn partial_cmp(&self, rhs: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(&rhs))
    }
}

#[derive(Clone, Debug)]
/// A type containing the necessary information to encode and decode text using huffman code
/// compression. this struct do not give a code point for every unicode char, instead it only give
/// one to the char present during the creation of the map.
pub struct HuffmanCodeMap(FxHashMap<CharOrRaw, BitBox>);

struct DecodeCodeMap(FxHashMap<BitBox, CharOrRaw>);

impl DecodeCodeMap {
    fn try_get_char_by_code(&self, bitslice: BitSliceRef) -> Option<&CharOrRaw> {
        let bit_box = bitslice.into_bitbox();
        let results = self.0.get(&bit_box);

        match results {
            Some(tuple) => Some(tuple),
            None => None,
        }
    }
}

impl HuffmanCodeMap {
    ///create a new HuffmanCodeMap witch is optimal for the given text
    /// it will treat a slice of byte as mostly valid ut8.
    /// # panic
    /// panic if the slice is zero byte wide
    pub fn new<I: Iterator<Item = Result<u8, anyhow::Error>>>(iterator: I) -> anyhow::Result<Self> {
        let mut char_list = BTreeMap::new();
        char_list
            .entry(CharOrRaw::Raw(Box::new(END_OF_FILE)))
            .or_insert(1);

        //cont each occurrence of a char or invalid byte
        for ch in CharsOrRaws::new(iterator) {
            *char_list.entry(ch?).or_insert(0) += 1;
        }

        let mut heap = BinaryHeap::new();

        //transform the hashmap into a binary heap of tree node
        for counted_char in char_list {
            heap.push(Node {
                frequency: counted_char.1,
                kind: NodeKind::Leaf(counted_char.0.into()),
            });
        }

        while heap.len() > 1 {
            //this code will only run if there at least 2 item in the heap
            //thus the 2 unwrap are fine
            let left_chill = heap.pop().unwrap();
            let right_chill = heap.pop().unwrap();
            heap.push(Node::merge(left_chill, right_chill));
        }


        let map = FxHashMap::default();
        let mut code = HuffmanCodeMap { 0: map };
        generate_codes(&heap.pop().unwrap(), BitVec::new(), &mut code);

        Ok(code)
    }

    fn get_char_code(&self, ch: CharOrRaw) -> anyhow::Result<BitSliceRef> {
        match self.0.get(&ch) {
            Some(code) => Result::Ok(code.as_bitslice()),
            None => bail!("Invalid data"),
        }
    }

    ///encode the String using the provided HuffmanCodeMap
    /// return error if there is a char in the String which is not present in the code map
    pub fn encode<R: io::Read, W: io::Write>(&self, input: R, mut output: W) -> anyhow::Result<()> {
        let mut buffer: BitVec = BitVec::new();
        let iter= input
            .bytes()
            .map(|result| { try { result?} });


        for ch in CharsOrRaws::new(iter) {
            let ch_cache = ch?;
            self.encode_char(ch_cache, &mut buffer)?;

            if buffer.len() >= 64 {
                flush_buffer(&mut buffer, &mut output)?;
            }
        }
        self.encode_char(CharOrRaw::Raw(Box::new(END_OF_FILE)), &mut buffer)?;

        let vec: Vec<u8> = buffer.into_vec();
        output.write_all(&vec)?;

        Result::Ok(())
    }

    fn reverse(self) -> DecodeCodeMap {
        let mut map = FxHashMap::default();

        for key_pair in self.0.into_iter() {
            map.entry(key_pair.1).or_insert(key_pair.0);
        }

        DecodeCodeMap(map)
    }

    fn encode_char(&self, ch: CharOrRaw, buffer: &mut BitVec) -> anyhow::Result<()> {
        let slice = self.get_char_code(ch.clone())
                                    .context("invalid data")?;

        buffer.extend_from_bitslice(slice);
        Ok(())
    }

    ///decode the string which was encoded with the code map.
    /// if you use the wrong HuffmanCodeMap to decode it will return a incorrect string
    pub fn decode<R: Iterator<Item=io::Result<u8>>, W: io::Write>(self, input: R, mut output: W) -> io::Result<()> {
        let map = self.reverse();

        let mut char_cache = BitVec::new();
        let mut binary_stream = Bits::new(input);
        let mut chache = [0; 5];

        while let Some(bit) = binary_stream.next() {
            let temp = bit?;
            char_cache.push(temp);
            if let Some(ch) = map.try_get_char_by_code(char_cache.as_bitslice()) {
                match ch {
                    CharOrRaw::Char(ch) => {
                        output.write_all(ch.encode_utf8(&mut chache).as_bytes())?;
                    }
                    CharOrRaw::Raw(raw) => {
                        if raw.len() == 5 {
                            return io::Result::Ok(());
                        } else {
                            output.write_all(&raw)?;
                        }
                    }
                }
                char_cache.clear();
            }
        }
        let mut iter = map.0.into_iter();
        /*while let Some(i) = iter.next() {
            eprintln!("box {:?}, ch {:?}", i.0, i.1);
        }*/
        drop(iter);

        drop(output);
        io::Result::Ok(())
    }
    
    ///serialize the given HuffmanCodeMap into a Vec<u8> using bincode
    pub fn serialize(self) -> Result<Vec<u8>, Box<bincode::ErrorKind>> {
        let mut output = FxHashMap::default();
        for pair in self.0.into_iter() {
            let bad_bit_box = pair.1.into_bad_bit_box();
            output.insert(pair.0, bad_bit_box);
        }
        bincode::serialize(&output)
    }

    
    ///deserialize a slice of u8 into a HuffmanCodeMap.
    ///it should have bean serialize with bincode otherwise it will yield a error
    pub fn deserialize(binary_stream: &[u8]) -> Result<HuffmanCodeMap, Box<bincode::ErrorKind>> {
        let map: FxHashMap<CharOrRaw, BadBitBox> = bincode::deserialize(binary_stream)?;
        let mut huffmap = FxHashMap::default();
        for (ch, bitbox) in map.into_iter() {
            huffmap.insert(ch, bitbox.into_bit_box());
        }
        Ok(HuffmanCodeMap(huffmap))
    }
}

fn flush_buffer<W: io::Write>(buffer: &mut BitVec, mut output: W) -> io::Result<()> {
    let sub_vec: Vec<u8> = buffer.get_full_bytes();

    output.write_all(&sub_vec)?;
    Ok(())
}

fn generate_codes(node: &Node, prefix: BitVec, out_codes: &mut HuffmanCodeMap) {
    return match &node.kind {
        NodeKind::Internal(ref left_child, ref right_child) => {
            let mut left_prefix = prefix.clone();
            left_prefix.push(false);
            generate_codes(&left_child, left_prefix, out_codes);

            let mut right_prefix = prefix;
            right_prefix.push(true);

            generate_codes(&right_child, right_prefix, out_codes);
        }
        NodeKind::Leaf(ch) => {
            out_codes.0.insert(ch.clone(), prefix.into_bitbox());
        }
    }
}

impl Node {
    pub fn merge(node1: Node, node2: Node) -> Node {
        let (bigger_node, smaller_node) = match node1.cmp(&node2) {
            Ordering::Less => (node2, node1.clone()),
            Ordering::Equal => (node1.clone(), node2),
            Ordering::Greater => (node1.clone(), node2.clone()),
        };

        Node {
            frequency: bigger_node.frequency + smaller_node.frequency,
            kind: NodeKind::Internal(
                Box::new(smaller_node.clone()),
                Box::new(bigger_node.clone()),
            ),
        }
    }
}

/*
mod test {
    use super::CharOrRaw;
    use super::HuffmanCodeMap;
    use super::END_OF_FILE;
    use super::{BitBox, BitVec};

    use std::collections::hash_map::HashMap;
    use std::iter;
    use rustc_hash::FxHashMap;
    use std::fs;
    use std::io::{stdout, Repeat};
    use std::io::BufReader;
    use std::io::Read;
    use std::thread;
    use std::iter::{Map, Once};


    #[test]
    fn encode_test() {
        let mut hash_map = FxHashMap::default();

        let a_slice = Box::new([0b01_00_00_00]);
        let b_slice = Box::new([0b00_00_00_00]);
        let eof_slice = Box::new([0b10_00_00_00]);

        hash_map.insert(CharOrRaw::Char('a'), BitBox::from_box(a_slice, 2));
        hash_map.insert(CharOrRaw::Char('b'), BitBox::from_box(b_slice, 2));

        hash_map.insert(
            CharOrRaw::Raw(Box::new(END_OF_FILE)),
            BitBox::from_box(eof_slice, 1),
        );

        let huff = HuffmanCodeMap(hash_map);

        let buffer = "ab".as_bytes();
        let mut output_buffer = vec![];

        huff.encode(buffer, &mut output_buffer).unwrap();

        assert_eq!(output_buffer, [0b01_00_10_00]) // "ab"
    }


    #[test]
    fn decode_test() {
        let mut hash_map = FxHashMap::default();

        let a_slice = Box::new([0b01_00_00_00]);
        let b_slice = Box::new([0b00_00_00_00]);
        let eof_slice = Box::new([0b10_00_00_00]);

        hash_map.insert(CharOrRaw::Char('a'), BitBox::from_box(a_slice, 2));
        hash_map.insert(CharOrRaw::Char('b'), BitBox::from_box(b_slice, 2));

        hash_map.insert(
            CharOrRaw::Raw(Box::new(END_OF_FILE)),
            BitBox::from_box(eof_slice, 1),
        );

        let huff = HuffmanCodeMap(hash_map);

        let buffer = [0b01_00_10_00]; // "ab"
        let mut output_buf = vec![];
        let bitvec = BitVec::from_vec(buffer.to_vec());

        huff.decode(buffer.as_ref(), &mut output_buf).unwrap();

        assert_eq!(output_buf, "ab".as_bytes())
    }


    #[test]
    fn html() {
        let mut encoded_data = vec![];
        let mut output_buffer = vec![];
        //let mut buffer: Vec<u8> = "bbbbbbbbbbbbbbbbbbbbbbbddddddduuV<>ddddddddddddd".as_bytes().to_vec();
        let mut buffer: Vec<u8> = "b".as_bytes().iter().cycle().take(23)
                                        .chain("d".as_bytes().iter().cycle().take(7))
                                        .chain("u".as_bytes().iter().cycle().take(2))
                                        .chain("V".as_bytes().iter())
                                        .chain("<".as_bytes().iter())
                                        .chain(">".as_bytes().iter())
                                        .chain("d".as_bytes().iter().cycle().take(13))
                                        .map(|e| *e)
                                        .collect();

        let iter = buffer.iter().map(|e| {anyhow::Result::Ok(*e)});

        let map = HuffmanCodeMap::new(iter).unwrap();

        map.encode(buffer.as_slice(), &mut encoded_data).unwrap();
        println!("encoded_data len {}", encoded_data.len());

        let test_iter: Vec<bool> = [true].iter().cycle().take(23 * 1) //b
            .chain([false, false].iter().cycle().take(7 * 2)) //d
            .chain([false, true, false, true].iter().cycle().take(2 * 4)) //u
            .chain([false, true, false, false, false].iter()) //V
            .chain([false, true, false, false, true].iter()) //<
            .chain([false, true, true, false].iter()) //>
            .chain([false, false].iter().cycle().take(13 * 2))//d
            .chain([false, true, true, true].iter()) //end
            .map(|e| *e).collect();

        let mut bitvec = BitVec::new();

        for bit in test_iter.into_iter() {
            bitvec.push(bit)
        }

        let test_buffer = bitvec.into_vec();

        assert_eq!(encoded_data, test_buffer, "encoded data");
        map.decode(encoded_data.as_slice(), &mut output_buffer).unwrap();

        assert_eq!(output_buffer, buffer, "end_resault");
    }


    #[test]
    fn invalid_utf8() {
        let mut file = fs::File::open("invalid_utf8_data").unwrap();
        let mut encoded_data = vec![];
        let mut output_buffer = vec![];
        let mut buffer = vec![];

        file.read_to_end(&mut buffer).unwrap();

        let iter = buffer.bytes().map(|e| try { e? });

        let map = HuffmanCodeMap::new(iter).unwrap();

        map.encode(buffer.as_slice(), &mut encoded_data).unwrap();

        map.decode(encoded_data.as_slice(), &mut output_buffer).unwrap();

        assert_eq!(output_buffer, buffer);
    }


    #[test]
    fn name() {
        let str = "ab";
        let buffer = BufReader::new(str.as_bytes());
        let mut mid_buffer = vec![];
        let mut out_buffer = vec![];
        let iter = buffer.bytes().map(|results| {
            Ok(results?)
        });

        let map = HuffmanCodeMap::new(iter).unwrap();

        let buffer = BufReader::new(str.as_bytes());

        map.encode(buffer, &mut mid_buffer).unwrap();

        map.decode(mid_buffer.as_slice(), &mut out_buffer).unwrap();
        assert_eq!(out_buffer, str.as_bytes().to_vec());
    }
}*/
