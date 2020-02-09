use std::collections::HashMap;
use std::collections::binary_heap::BinaryHeap;
use std::cmp::Ordering;
use serde::{Serialize, Deserialize};
use bitvec::prelude::*;
use unicode_normalization::UnicodeNormalization;
use bincode;
use bincode::deserialize;
use bstr;
use bstr::{CharOrRaw, BString, ByteVec};
use bstr::ByteSlice;
use crate::LocalCharOrRaw::Char;


#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
enum LocalCharOrRaw {
    Char(char),
    Raw(Box<[u8]>)
}


#[derive(Debug, Clone, Eq, PartialEq)]
enum NodeKind {
    Internal(Box<Node>, Box<Node>),
    Leaf(LocalCharOrRaw),
}

#[derive(Debug, Clone, Eq, PartialEq)]
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

impl From<CharOrRaw<'_>> for LocalCharOrRaw {
    fn from(ch: CharOrRaw) -> LocalCharOrRaw {
        match ch {
            CharOrRaw::Char(ch) => LocalCharOrRaw::Char(ch),
            CharOrRaw::Raw(raw_slice) => LocalCharOrRaw::Raw(raw_slice.into()),
        }
    }
}

#[derive(Clone, Serialize, Deserialize, Debug)]
/// A type containing the necessary information to encode and decode text using huffman code compression.
/// this struct do not give a code point for every unicode char, instead it only give one to the char
/// present during the creation of the map.
pub struct HuffmanCodeMap(HashMap<LocalCharOrRaw, BitBox<Lsb0, u8>>);

impl HuffmanCodeMap {
    ///create a new HuffmanCodeMap witch is optimal for the given text
    /// it will treat a slice of byte as mostly valid ut8.
    /// # panic
    /// panic if the slice is zero byte wide
    pub fn new(text: &[u8]) -> Self {
        if text.len() == 0 {panic!("Bug zero len wide string cannot be use to create a HuffmanCodeMap")}
        
        let mut char_list = HashMap::new();

        //cont each occurrence of a char or invalid byte
        for ch in text.chars_or_raws() {
            *char_list.entry(ch).or_insert(0) += 1;
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

        let mut code = HuffmanCodeMap {0: HashMap::new()};
        generate_codes(&heap.pop().unwrap(), BitVec::new(), &mut code);
    
        code
    }

    fn get_char_code(&self, ch: LocalCharOrRaw) -> Result<BitBox<Lsb0, u8>, ()> {
        let code_option = self.0.get(&ch).cloned();
        match code_option {
            Some(code) => Result::Ok(code),
            None => Result::Err(()),
            
        }
    }

    ///encode the String using the provided HuffmanCodeMap
    /// return error if there is a char in the String which is not present in the code map
    pub fn encode(&self, text: &[u8]) -> Result<Vec<u8>, ()> {
        let mut output_stream: BitVec<Lsb0, u8> = BitVec::new();

        for ch in text.chars_or_raws() {
            output_stream.extend_from_slice((&mut self.get_char_code(ch.into())?))
        }

        let len = output_stream.len();
        let mut output_stream = output_stream.into_vec();

        output_stream.insert(0, 8-(len % 8) as u8);

        Result::Ok(output_stream)
    }

    fn try_get_char_by_code(&self, bitslice: &BitSlice) -> Option<LocalCharOrRaw> {
        let results = self.0.iter().find(|pair| {
            pair.1 == bitslice
        });

        match results {
            Some(tuple) => Some(tuple.0.clone()),
            None => None,
        }
    }

    ///decode the string which was encoded with the code map.
    /// if you use the wrong HuffmanCodeMap to decode it will return a incorrect string
    pub fn decode(&self, bytes_stream: &[u8]) -> Vec<u8> {
        let alignment = *bytes_stream.first().unwrap();

        let (_, bytes_stream) = bytes_stream.split_first().unwrap();

        let mut binary_stream: BitBox<Lsb0, u8> = BitBox::from_slice(bytes_stream);
        let mut str_cache: Vec<u8>  = vec![];
        let mut char_cache: BitVec = BitVec::new();

        let binary_stream = &binary_stream[..binary_stream.len() - alignment as usize];
        
        for bit in binary_stream.iter() {

            char_cache.push(*bit);
            if let Some(ch) = self.try_get_char_by_code(&char_cache) {
                match ch {
                    LocalCharOrRaw::Char(ch) => str_cache.push_char(ch),
                    LocalCharOrRaw::Raw(raw) => str_cache.append(&mut raw.to_vec()),
                }
                char_cache.clear();
            }
        }
        str_cache

    }


    ///serialize the given HuffmanCodeMap into a Vec<u8> using bincode
    pub fn serialize(&self) -> Result<Vec<u8>, Box<bincode::ErrorKind>> {
        bincode::serialize(self)
    }


    ///deserialize a slice of u8 into a HuffmanCodeMap.
    ///it should have bean serialize with bincode otherwise it will yield a error
    pub fn deserialize(binary_stream: &[u8]) -> Result<HuffmanCodeMap, Box<bincode::ErrorKind>> {
        bincode::deserialize(binary_stream)
    }
}

fn generate_codes(node: &Node, prefix: BitVec<Lsb0, u8>, out_codes: &mut HuffmanCodeMap) {

    match &node.kind {
        NodeKind::Internal(ref left_child, ref right_child) => {
            let mut left_prefix = prefix.clone();
            left_prefix.push(false);
            generate_codes(&left_child, left_prefix, out_codes);
 
            let mut right_prefix = prefix;
            right_prefix.push(true);

            generate_codes(&right_child, right_prefix, out_codes);
        }
        NodeKind::Leaf(ch) => {
            out_codes.0.insert(ch.clone(), BitBox::from(prefix));
        }
    }
}

impl Node {
    pub fn merge(node1: Node, node2: Node) -> Node {
        let (bigger_node, smaller_node) = match node1.cmp(&node2) {
            Ordering::Less => {(node2, node1.clone())},
            Ordering::Equal => (node1.clone(), node2),
            Ordering::Greater => (node1.clone(), node2.clone()),
        };

        Node {
            frequency: bigger_node.frequency + smaller_node.frequency,
            kind: NodeKind::Internal(Box::new(smaller_node.clone()), Box::new(bigger_node.clone())),
        }
    }
}


mod test {
    use super::HuffmanCodeMap;
    use std::fs::File;
    use std::io::Read;

    #[test]
    fn invalid_utf8() {
        let mut file = File::open("invalid_utf8_data").unwrap();
        let mut buffer: Vec<u8> = vec![];
        file.read_to_end(&mut buffer).unwrap();

        let map = HuffmanCodeMap::new(&buffer);
        let mut encoded_data = map.encode(&buffer).unwrap();

        let output_buffer = map.decode(&mut encoded_data);

        assert_eq!(output_buffer, buffer);

    }

    #[test]
    fn name() {
        let s = "abbccccdddddeeeeee";
        let map = HuffmanCodeMap::new(s.as_bytes());
        let code = map.encode(s.as_bytes());
        let ss = map.decode( &mut code.unwrap());
        assert_eq!(s.as_bytes().to_vec(), ss);
    }

    #[test]
    #[should_panic]
    fn zero_size_string_for_huffman_code_map() {
        HuffmanCodeMap::new(&[]);
    }
}
