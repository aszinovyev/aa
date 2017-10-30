extern crate aa;

use aa::a;
use std::io;

fn main() {
  let mut n = String::new();
  io::stdin().read_line(&mut n).unwrap();
  let n = n.trim().parse().unwrap();

  let mut perm = a::Permutation::new(n);

  while {
    println!("{:?}", perm.get());
    perm.next();
    perm.get() != []
  } {}
}
