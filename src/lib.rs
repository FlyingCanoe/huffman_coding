use std::iter::*;
use std::iter;
use std::cmp::Reverse;
use std::collections::BinaryHeap;
#[macro_use] extern crate failure;

pub mod io;
mod iterator;

#[derive(Debug, Clone)]
pub struct SplitPoint {
    //a one
    one: Node,
    // a zero
    zero: Node,
}

impl SplitPoint {
    pub fn new(n1: Node, n2: Node) -> Self {
        SplitPoint {
            one: n1,
            zero: n2,
        }
    }
}

fn add_char(node_list: &mut Vec<Node>, ch: char) {
    for node in node_list.iter_mut() {

        if node.char().unwrap() == ch {

            match node {
                Node::Leaf(num, ..) => {
                    *num += 1;
                    return 
                }
                Node::Internal(..) => {unreachable!()},
            }
        }
    }
    //the char is not in the list if the return in the for loop is not triger
    node_list.push(Node::Leaf(1, ch, vec!()));
}

impl From<String> for Node {
    fn from(s: String) -> Self {
        let mut char_list: Vec<Node> = vec!(); 
        for ch in s.chars() {
            add_char(&mut char_list, ch);
            println!("node list (");
            for node in char_list.clone() {
                println!("{}", node)
            }
        }

        let mut heap: BinaryHeap<Node> = char_list.into_iter().collect();
        
        println!("{:?}", heap);
        while let (Some(node1), Some(node2)) = (heap.pop(), heap.pop()) {
            heap.push(Node::merge(node1, node2));
            if heap.len() == 1 {
                break
            }
            println!("node list merge in progress (");
            for node in heap.clone() {
                println!("{}", node)
            }
        }

        heap.pop().unwrap()
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Leaf(usize, char, Vec<bool>),
    Internal(usize, Box<SplitPoint>, Vec<bool>),
}



impl Node { 
    pub fn num(&self) -> usize {
        match self {
            Node::Leaf(num, _, _) => {*num},
            Node::Internal(num, _, _) => {*num},
        }
    }

    ///return the char of the node if it is a leaf node
    pub fn char(&self) -> Option<char> {
        match self {
            Node::Leaf(_, ch, _) => {Some(*ch)},
            Node::Internal(_, _, _) => {None}
        }
    }

    pub fn append_to_path(&mut self, b: bool) {
        match self {
            Node::Internal(_, _, vec) => {vec.push(b);},
            Node::Leaf(_, _, vec) => {vec.push(b);}
        }
        
    }
}

impl Node {
    pub fn merge(mut self, mut other: Node) -> Node {
        //if node 1 is biger
        if self > other {
            //add True to the node 1 path
            self.append_to_path(true);

            //ad False to the node 2 path
            other.append_to_path(false);

            let n: Node = Node::Internal(
                self.num() + other.num(),
                Box::new(
                    SplitPoint {
                        one: self,
                        zero: other.clone(),
                    }
                ),
                vec!(),
            );
            n
        }
        else {
            other.append_to_path(true);
            self.append_to_path(false);

            Node::Internal(
                self.num() + other.num(),
                Box::new(
                    SplitPoint {
                        one: other,
                        zero: self,
                    }
                ),
                vec!()
            )
        }
    }
}

mod test {
    use super::*;

    #[test]
    fn add_char_fn_test() {
        let mut node_list: Vec<Node> = vec!();
        add_char(&mut node_list, 'a');
        add_char(&mut node_list, 'a');
        add_char(&mut node_list, 'a');
        add_char(&mut node_list, 'b');
        add_char(&mut node_list, 'b');
        add_char(&mut node_list, 'c');

        assert_eq!(node_list, vec!(
            Node::Leaf(
                3,
                'a',
                vec!()
            ),
            Node::Leaf(
                2,
                'b',
                vec!()
            ),
            Node::Leaf(
                1,
                'c',
                vec!()
            )
        ))
    }

    #[test]
    fn node_from_string() {
        let s: String = String::from("aaaabbc");
        let node = Node::from(s);

        match node {
            //there are more than one 3 type of char in s ('a' 'b' and 'c')
            //so it should be a internal leaf
            Node::Leaf(..) => {panic!()},

            Node::Internal(_, split, _) => {
                match &split.one {

                    Node::Internal(..) => panic!(),

                    Node::Leaf(num, ch, path) => {
                        assert_eq!(*num, 4);
                        assert_eq!(*ch, 'a');
                        assert_eq!(*path, vec!(true));
                    },
                }
                match &split.zero {
                    Node::Leaf(..) => panic!(),

                    Node::Internal(_, sub_split, _) => {
                        match &sub_split.one {
                            Node::Internal(..) => panic!(),
                            Node::Leaf(num, ch, path) => {
                                assert_eq!(*num, 2);
                                assert_eq!(*ch, 'b');
                                //assert_eq!(*path, vec!(false, true));
                            }
                        }

                        match &sub_split.zero {
                            Node::Internal(..) => panic!(),
                            Node::Leaf(num, ch, path) => {
                                assert_eq!(*num, 1);
                                assert_eq!(*ch, 'c');
                                assert_eq!(*path, vec!(false, false))
                            }
                        }
                    },
                }
            }
        }
    }

    #[test]
    fn partily_internal_merge_test() {
        let n1 = Node::Internal(
            3,
            Box::new(
                SplitPoint {
                    zero: Node::Leaf(1, 'c', vec!(false)),
                    one: Node::Leaf(2, 'b', vec!(true)),
                }
            ),
            vec!()
        );

        let n2 = Node::Leaf(5, 'a', vec!());

        let n3 = Node::merge(n1, n2);

        match n3 {
            Node::Leaf(..) => {panic!()},
            Node::Internal(num, split, _) => {
                assert_eq!(num, 8);

                match split.one {
                    Node::Internal(..) => panic!(),
                    Node::Leaf(num, ch, path) => {
                        assert_eq!(num, 5);
                        assert_eq!(ch, 'a');
                        assert_eq!(path, vec!(true));
                    }
                }

                match split.zero {
                    Node::Leaf(..) => panic!(),
                    Node::Internal(num, sub_split, path) => {
                        assert_eq!(num, 3);
                        assert_eq!(path, vec!(false));

                        match sub_split.one {
                            Node::Internal(..) => panic!(),
                            Node::Leaf(num, ch, path) => {
                                assert_eq!(num, 2);
                                assert_eq!(ch, 'b');
                                assert_eq!(path, vec!(false, true));
                            }
                        }

                        match sub_split.zero {
                            Node::Internal(..) => panic!(),
                            Node::Leaf(num, ch, path) => {
                                assert_eq!(num, 1);
                                assert_eq!(ch, 'c');
                                assert_eq!(path, vec!(false, false))
                            }
                        }
                    } 
                }
            }
        }
    }

    #[test]
    fn leaf_merge_test() {
        let n1 = Node::Leaf(2, 'a', vec!());
        let n2 = Node::Leaf(1, 'b', vec!());

        let n3 = Node::merge(n1, n2);

        if let Node::Internal(num, node, _) = n3 {
            assert_eq!(num, 3);
            if let Node::Leaf(num_one, ch_one, path_one) = &node.one {
                assert_eq!(*num_one, 2);
                assert_eq!(*ch_one, 'a');
                assert_eq!(*path_one, vec!(true))
            }
            else {panic!()}

            if let Node::Leaf(num_zero, ch_zero, path_zero) = &node.zero {
                assert_eq!(*num_zero, 1);
                assert_eq!(*ch_zero, 'b');
                assert_eq!(*path_zero, vec!(false))
            }
            else {panic!()}
        };
    }
}

mod node_eq {
    use std::cmp::Ordering;
    use super::*;

    impl PartialEq for Node {
        fn eq(&self, other: &Node) -> bool {
            self.num() == other.num()
        }
    }

    impl Eq for Node {}

    impl Ord for Node {
        fn cmp(&self, other: &Node) -> Ordering {
            self.num().cmp(&other.num())
        }
    }

    impl PartialOrd for Node {
        fn partial_cmp(&self, other: &Node) -> Option<Ordering> {
            self.num().partial_cmp(&other.num())
        }
    }
}

mod node_fmt {
    use super::Node;
    use std::fmt;

    impl fmt::Display for Node {
        fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            match self {
                Node::Leaf(num, ch, _) => {writeln!(f, "'{}': {}", ch, num)}
                Node::Internal(_, split, _) => {
                    for leaf in split.clone().into_iter() {
                        match leaf {
                            Node::Leaf(num, ch, _) => {writeln!(f, "'{}': {}", ch, num)?;},
                            Node::Internal(..) => {unreachable!()},
                        }
                    }
                    write!(f, "")
                }
            }
        }
    }
}