use super::*;
use failure;

#[derive(Clone, Debug)]
pub struct TreeLeaf {
    ch: char,
    path: Vec<bool>
}

#[derive(Clone, Debug)]
pub struct Tree {
   pub leaf_list: Vec<TreeLeaf>,
}

impl Tree {
    fn try_get(self, path: &Vec<bool>) -> Option<TreeLeaf> {
        self.leaf_list.into_iter().find(|leaf| {
            leaf.path == *path
        })
    }
}

impl From<String> for Tree {
    fn from(s: String) -> Self {
        let node = Node::from(s);
        Tree {
            leaf_list: node.into_iter().map(|node| {
                match node {
                    Node::Leaf(_, ch, path) => {
                        TreeLeaf {
                            ch,
                            path
                        }
                    }
                    _ => {unreachable!()}
                }
            }).collect()
        }
    }
}

pub struct EncodedStream {
    stream: Vec<bool>,
}

impl EncodedStream {
    pub fn decode(mut self, t: Tree) -> Result<String   , failure::Error> {
        let mut char_list: Vec<char> = vec!();
        let mut binery_slice: Vec<bool> = vec!();
        self.stream.reverse();
        while let Some(b) = self.stream.pop() {
            binery_slice.push(b);
            if let Some(leaf) = t.clone().try_get(&binery_slice) {
                char_list.push(leaf.ch);
                binery_slice.clear();
            }

        }

        if !binery_slice.is_empty() {
            bail!("");
        }
        Result::Ok(char_list.into_iter().collect())

    }
}

impl Tree {
    pub fn encode(self, s: String) -> Result<EncodedStream, failure::Error> {
        let iter = s.chars().map(|ch| {
            self.clone().into_iter().find(|tree_leaf| {
                tree_leaf.ch == ch
            })
        });
        let mut binary_char_list: Vec<Vec<bool>> = vec!();
        for leaf in iter {
            match leaf {
                Some(leaf) => {binary_char_list.push(leaf.path.to_vec())},
                _ => {bail!("")}
            }
        }

        let mut stream: Vec<bool> = vec!();

        for  binary_char in binary_char_list {
            stream.append(&mut binary_char.into_iter().collect())
        }
        Result::Ok(
            EncodedStream {
                stream,
            }
        )
    }
}