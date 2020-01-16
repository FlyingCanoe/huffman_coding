use std::collections::BTreeMap;
use std::collections::binary_heap::BinaryHeap;
use std::cmp::Ordering;
use bitvec::prelude::*;

pub mod io;

#[macro_use] extern crate failure;   



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

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord)]
pub struct HuffmanCodeMap(BTreeMap<char, BitVec>);


impl HuffmanCodeMap {
    pub fn new(text: String) -> Self {
        
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
            let left_chill = heap.pop().unwrap(); 
            let right_chill = heap.pop().unwrap();
            heap.push(Node::merge(left_chill, right_chill));
            if heap.len() == 1 {
                break
            }
        }

        let mut code = HuffmanCodeMap {0: BTreeMap::new()};
    generate_codes(&heap.pop().unwrap(), BitVec::new(), &mut code);
    
    code
    }
    pub fn get_char_code(&self, ch: char) -> Result<BitVec, ()> {
        let code_option = self.0.get(&ch).cloned();
        match code_option {
            Some(code) => Result::Ok(code),
            None => Result::Err(()),
            
        }
    }
    
    pub fn encode(&self, text: String) -> Result<BitVec, ()> {
        let char_code_list = text
            .chars()
            .map(|ch| { self.get_char_code(ch) });

        let mut output_stream = BitVec::new();
        for vec in char_code_list {
            output_stream.append(&mut vec?);
        }
        Result::Ok(output_stream)
    }

    fn try_get_char_by_code(&self, bitvec: &BitVec) -> Option<char> {
        let resault = self.0.iter().find(|pair| {
            pair.1 == bitvec 
        });

        match resault {
            Some(tuple) => Some(*tuple.0),
            None => None,
        }
    }

    pub fn decode(&self, mut binary_stream: BitVec) -> String {
        let mut str_chache = String::new();
        let mut char_chache: BitVec = BitVec::new();
        
        while !binary_stream.is_empty() {
            char_chache.push(*binary_stream.first().unwrap());
            binary_stream.remove(0);
            if let Some(ch) = self.try_get_char_by_code(&char_chache) {
                str_chache.push(ch);
                char_chache.clear();
            }
        }
        str_chache

    }
}

fn generate_codes(node: &Node, prefix: BitVec, out_codes: &mut HuffmanCodeMap) {

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
        let (bigger_node, smaler_node) = match node1.cmp(&node2) {
            Ordering::Less => {(node2, node1)},
            Ordering::Equal => (node1, node2),
            Ordering::Greater => (node1, node2),
        };

        Node {
            frequency: bigger_node.frequency + smaler_node.frequency,
            kind: NodeKind::Internal(Box::new(smaler_node), Box::new(bigger_node)),
        }
    }
}


mod test {
    use bitvec::prelude::*;
    use super::{Node, NodeKind, HuffmanCodeMap};

    #[test]
    fn name() {
        let s = "abbccccdddddeeeeee";
        let map = HuffmanCodeMap::new(String::from(s));
        let code = map.encode(String::from(s));
        let ss = map.decode(code.unwrap());
        assert_eq!(s, ss);

        

    }

    /*
    #[test]
    fn partily_internal_merge_test() {
        let n1 = Node {
            frequency: 3,
            kind: NodeKind::Internal(
                Box::new(
                    Node {
                        frequency: 1,
                        kind: NodeKind::Leaf('c'),
                    }
                ),
                Box::new(
                    Node {
                        frequency: 1,
                        kind: NodeKind::Leaf('b'),
                    }
                )
            ),
        };

        let n2 = Node {
            frequency: 5,
            kind: NodeKind::Leaf('a'),
        };

        let n3 = Node::merge(n1, n2);
        assert_eq!(n3.frequency, 8);

        match n3.kind {
            NodeKind::Leaf(..) => {panic!()},
            NodeKind::Internal(left_child, right_child) => {
                assert_eq!(left_child.frequency, 3);
                assert_eq!(right_child.frequency, 5);

                match right_child.kind {
                    NodeKind::Internal(..) => panic!(),
                    NodeKind::Leaf(ch) => {
                        assert_eq!(ch, 'a');
                    }
                }

                match left_child.kind {
                    NodeKind::Leaf(..) => panic!(),
                    NodeKind::Internal(left_child, right_child) => {
                        assert_eq!(left_child.frequency, 1);
                        assert_eq!(right_child.frequency, 2);

                        match right_child.kind {
                            NodeKind::Internal(..) => panic!(),
                            NodeKind::Leaf(ch) => {
                                assert_eq!(ch, 'b');
                            }
                        }

                        match left_child.kind {
                            NodeKind::Internal(..) => panic!(),
                            NodeKind::Leaf(ch) => {
                                assert_eq!(ch, 'c');
                            }
                        }
                    } 
                }
            }
        }
    }

    #[test]
    fn leaf_merge_test() {
        let n1 = Node {
            frequency: 2,
            kind: NodeKind::Leaf('a'),
        };

        let n2 = Node {
            frequency: 1,
            kind: NodeKind::Leaf('b'),
        };

        let n3 = Node::merge(n1, n2);

        assert_eq!(n3.frequency, 3);

        match n3.kind {
            NodeKind::Leaf(..) => panic!(),

            NodeKind::Internal(left_child, right_child) => {
                assert_eq!(left_child.frequency, 1);
                assert_eq!(right_child.frequency, 2);

                match right_child.kind {
                    NodeKind::Leaf(ch) => assert_eq!(ch, 'a'),
                    NodeKind::Internal(..) => panic!(),
                }

                match left_child.kind {
                    NodeKind::Leaf(ch) => assert_eq!(ch, 'b'), 
                    NodeKind::Internal(..) => panic!(),
                }
            }
        }
    }*/
}