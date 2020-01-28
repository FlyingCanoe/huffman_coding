use std::collections::BTreeMap;
use std::collections::binary_heap::BinaryHeap;
use std::cmp::Ordering;
use serde::{Serialize, Deserialize};
use bitvec::prelude::*;
use unicode_normalization::UnicodeNormalization;
use bincode;
use bincode::deserialize;


#[derive(Debug, Clone, Eq, PartialEq)]
enum NodeKind {
    Internal(Box<Node>, Box<Node>),
    Leaf(char),
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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Serialize, Deserialize)]
/// A type containing the necessary information to encode and decode text using huffman code compression.
/// this struct do not give a code point for every unicode char, instead it only give one to the char
/// present during the creation of the map.
pub struct HuffmanCodeMap(BTreeMap<char, BitVec<Lsb0, u8>>);


impl HuffmanCodeMap {
    ///create a new HuffmanCodeMap witch is optimal for the given string
    /// # panic
    /// panic if the string is zero char wide
    pub fn new(text: &String) -> Self {
        let text = text.nfc().collect::<String>();
        if text.len() == 0 {panic!("Bug zero len wide string cannot be use to create a HuffmanCodeMap")}
        
        let mut char_list = BTreeMap::new();
        for ch in text.chars() {
            *char_list.entry(ch).or_insert(0) += 1;
        }

        let mut heap = BinaryHeap::new();
        for counted_char in char_list {
            heap.push(Node {
                frequency: counted_char.1,
                kind: NodeKind::Leaf(counted_char.0),
            });
        }
        
        while heap.len() > 1 {
            //this code will only run if there at least 2 item in the heap
            //thus the 2 unwrap are fine
            let left_chill = heap.pop().unwrap(); 
            let right_chill = heap.pop().unwrap();
            heap.push(Node::merge(left_chill, right_chill));
        }

        let mut code = HuffmanCodeMap {0: BTreeMap::new()};
        generate_codes(&heap.pop().unwrap(), BitVec::new(), &mut code);
    
        code
    }

    fn get_char_code(&self, ch: char) -> Result<BitVec<Lsb0, u8>, ()> {
        let code_option = self.0.get(&ch).cloned();
        match code_option {
            Some(code) => Result::Ok(code),
            None => Result::Err(()),
            
        }
    }

    ///encode the String using the provided HuffmanCodeMap
    /// return error if there is a char in the String which is not present in the code map
    pub fn encode(&self, text: String) -> Result<Vec<u8>, ()> {
        let text = text.nfc().collect::<String>();
        let char_code_list = text
            .chars()
            .map(|ch| { self.get_char_code(ch) });

        let mut output_stream: BitVec<Lsb0, u8> = BitVec::new();
        for vec in char_code_list {
            output_stream.append(&mut vec?);
        }
        Result::Ok(output_stream.into_vec())
    }

    fn try_get_char_by_code(&self, bitvec: &BitVec) -> Option<char> {
        let results = self.0.iter().find(|pair| {
            pair.1 == bitvec
        });

        match results {
            Some(tuple) => Some(*tuple.0),
            None => None,
        }
    }

    ///decode the string which was encoded with the code map.
    /// if you use the wrong HuffmanCodeMap to decode it will return a incorrect string
    pub fn decode(&self, bytes_stream: &[u8]) -> String {
        let mut binary_stream: BitVec<Lsb0, u8> = BitVec::from_slice(bytes_stream);
        let mut str_cache = String::new();
        let mut char_cache: BitVec = BitVec::new();

        binary_stream.reverse();
        while !binary_stream.is_empty() {
            // when the binary_stream is empty it will break
            // thus the unwrap is fine
            char_cache.push(binary_stream.pop().unwrap());
            //binary_stream.remove(0);
            if let Some(ch) = self.try_get_char_by_code(&char_cache) {
                sir_cache.push(ch);
                char_cache.clear();
            }
        }
        sir_cache

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

    match node.kind {
        NodeKind::Internal(ref left_child, ref right_child) => {
            let mut left_prefix = prefix.clone();
            left_prefix.push(false);
            generate_codes(&left_child, left_prefix, out_codes);
 
            let mut right_prefix = prefix;
            right_prefix.push(true);

            generate_codes(&right_child, right_prefix, out_codes);
        }
        NodeKind::Leaf(ch) => {
            out_codes.0.insert(ch, prefix);
        }
    }
}

impl Node {
    pub fn merge(node1: Node, node2: Node) -> Node {
        let (bigger_node, smaller_node) = match node1.cmp(&node2) {
            Ordering::Less => {(node2, node1)},
            Ordering::Equal => (node1, node2),
            Ordering::Greater => (node1, node2),
        };

        Node {
            frequency: bigger_node.frequency + smaller_node.frequency,
            kind: NodeKind::Internal(Box::new(smaller_node), Box::new(bigger_node)),
        }
    }
}


mod test {
    use super::HuffmanCodeMap;

    #[test]
    fn name() {
        let s = "abbccccdddddeeeeee";
        let map = HuffmanCodeMap::new(&String::from(s));
        let code = map.encode(String::from(s));
        let ss = map.decode( &code.unwrap());
        assert_eq!(s, ss);
    }

    #[test]
    #[should_panic]
    fn zero_size_string_for_huffman_code_map() {
        HuffmanCodeMap::new(&"".into());
    }
}