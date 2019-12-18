use super::*;
use super::io;
use std::vec;

pub struct TreeIter {
    iter: vec::IntoIter<io::TreeLeaf>,
}

impl IntoIterator for io::Tree {
    type Item = io::TreeLeaf;
    type IntoIter = TreeIter;

    fn into_iter(self) -> TreeIter {
        TreeIter {
            iter: self.leaf_list.into_iter(),
        }
    }
}

impl Iterator for TreeIter {
    type Item = io::TreeLeaf;

    fn next(&mut self) -> Option<io::TreeLeaf> {
        self.iter.next()
    }
}

//consume a split point return a iterator
impl IntoIterator for SplitPoint {
    type Item = Node;
    type IntoIter = iter::Chain<NodeIterator, NodeIterator>;

    fn into_iter(self) -> Chain<NodeIterator, NodeIterator> {
        self.zero.into_iter().chain(self.one.into_iter())
    }
}

//consume a node return a iterator
impl IntoIterator for Node {
    type Item = Node;
    type IntoIter = NodeIterator;

    fn into_iter(self) -> NodeIterator {
        NodeIterator {
            node: self,
            iter: None,
            index: 0,
            is_finise: false,
        }
    }
}

#[derive(Clone)]
pub struct NodeIterator {
    node: Node,
    iter: Option<Box<iter::Chain<NodeIterator, NodeIterator>>>,
    index: usize,
    is_finise: bool,
}

impl Iterator for NodeIterator {
    type Item = Node;
    fn next(&mut self) -> Option<Node> {
        if self.is_finise {
            return None
        }
        if let Some(iter) = &mut self.iter {
            let val = iter.nth(self.index);
            self.index += 1;
            val
        }
        else {
            self.iter = match &self.node {
                Node::Leaf(_, _, _) => {
                    self.is_finise = true;
                    return Some(self.node.clone())
                }
                Node::Internal(_, split, _) => {
                    Some(Box::new(split.zero.clone().into_iter().chain(split.one.clone().into_iter())))
                } 
            };
        let val = self.iter.clone().unwrap().nth(self.index);
        self.index += 1;
        val 
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn internal_split_point_iter() {
        let mut s = SplitPoint {
            one: Node::Leaf(4, 'a', vec!(true)),
            zero: Node::Internal(3, Rc::new(
                SplitPoint {
                    one: Node::Leaf(2, 'b', vec!(false, true)),
                    zero: Node::Leaf(1, 'c', vec!(false, false))
                }
                ),
                vec!(false)
            )         
        }.into_iter();

        //item 0
        //(Leaf(1, 'c', vec(false, false)))
        match s.next().unwrap() {
            Node::Leaf(num, ch, path) => {
                assert_eq!(num, 1);
                assert_eq!(ch, 'c');
                assert_eq!(path, vec!(false, false));
            },
            Node::Internal(_, _, _) => {panic!()}
        }

        //item 1
        //(internal(2, 'b' , vec!(false, true) ))
        match s.next().unwrap() {
            Node::Leaf(num, ch, path) => {
                assert_eq!(num, 2);
                assert_eq!(ch, 'b');
                assert_eq!(path, vec!(false, true));
            },
            Node::Internal(_, _, _) => {panic!()}
        }

        //item2
        //leaf(4, a, vec(true))
        match s.next().unwrap() {
            Node::Leaf(num, ch, path) => {
                assert_eq!(num, 4);
                assert_eq!(ch, 'a');
                assert_eq!(path, vec!(true));
            },
            Node::Internal(_, _, _) => {panic!()}
        }
    }

    #[test]
    fn all_leaf_split_point_iter() {
        let mut s = SplitPoint {
            zero: Node::Leaf(1, 'b', vec!(false)),
            one:  Node::Leaf(2, 'a', vec!(true)),
        }.into_iter();

        if let Node::Leaf(num, ch, _) = s.next().unwrap() {
            if num !=  1  {panic!()}
            if ch  != 'b' {panic!()}
        }

        if let Node::Leaf(num, ch, _) = s.next().unwrap() {
            if num !=  2  {panic!()}
            if ch  != 'a' {panic!()}
        }

    }

    #[test]
    fn leaf_node_iter() {
        let mut n = Node::Leaf(1, 'a', vec!()).into_iter();

        if let Node::Leaf(num, item, _) = n.next().unwrap() {
            if num != 1 {panic!()}
            if item != 'a' {panic!()}
        }
        else {
            panic!()
        }
    }
}