use std::rc::Rc;
use std::iter::*;
use std::iter;
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
        let mut node_list: Vec<Node> = Vec::with_capacity(s.len());
        for ch in s.chars() {
            add_char(&mut node_list, ch)
        }
        node_list.sort_unstable();
        while let (Some(node1), Some(node2)) = (node_list.pop(), node_list.pop()) {
            node_list.push(Node::merge(node1, node2));
            node_list.sort_unstable();
        }
        node_list.pop().unwrap()
    }
}

#[derive(Debug, Clone)]
pub enum Node {
    Leaf(usize, char, Vec<bool>),
    Internal(usize, Rc<SplitPoint>, Vec<bool>),
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


    pub fn merge(mut n1: Node, mut n2: Node) -> Node {
        //if node 1 is biger
        if n1 > n2 {
            //add True to the node 1 path
            n1.append_to_path(true);

            //ad False to the node 2 path
            n2.append_to_path(false);        
            Node::Internal(n1.num() + n2.num(), Rc::new(
                SplitPoint {
                    one: n1,
                    zero: n2,
                }
            ),
            vec!(),
            )
        }
        else {
            n2.append_to_path(true);
            n1.append_to_path(false);

            Node::Internal(n1.num() + n2.num(), Rc::new(
                SplitPoint {
                    one: n2,
                    zero: n1,
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