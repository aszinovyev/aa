extern crate aa;

use aa::aa::*;
use std::io;

fn main() {
  let mut n = String::new();
  io::stdin().read_line(&mut n).unwrap();
  let n = n.trim().parse().unwrap();

  println!("{:?}", Group::with_size(n));
}
