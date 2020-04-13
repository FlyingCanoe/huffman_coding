use std::fs;
use std::io::BufReader;
use std::io::BufWriter;
use std::io::Read;
use std::mem;

use huffman_coding::HuffmanCodeMap;
use huffman_coding::bitvec1::{BitVec, BitBox};

fn main() {
    let file = fs::File::open("dna.50MB").unwrap();
    let dump = BufWriter::new(fs::File::create("dump").unwrap());
    let buff = BufReader::new(&file)
        .bytes()
        .map(|results| -> anyhow::Result<u8> {
            anyhow::Result::Ok(results?)
        });
    let code = HuffmanCodeMap::new(buff).unwrap();
    let num = mem::size_of::<Box<u8>>();

    println!("size {}", num);

    let file2 = fs::File::open("dna.50MB").unwrap();
    let buff2 = BufReader::new(file2);
    code.encode(buff2, dump);
    println!("decode now");

    let file3 = fs::File::open("dump").unwrap();
    let buf3 = BufReader::new(file3);

    let dump2 = BufWriter::new(fs::File::create("dump2").unwrap());

    code.decode(buf3, dump2);
}