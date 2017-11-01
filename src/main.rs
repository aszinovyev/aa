extern crate aa;

use aa::aa::*;
use std::io;

fn main() {
  let mut n = String::new();
  io::stdin().read_line(&mut n).unwrap();
  let n: u32 = n.trim().parse().unwrap();

  // println!("{:?}", Group::with_size(n));

  let mut groups = Vec::new();
  for i in 1..(n + 1) {
    groups.append(&mut Group::with_size(i));
  }
  println!("Finished generating groups.");

  let mut handles = Vec::new();

  for i in 0..groups.len() {
    for j in (i + 1)..groups.len() {
      for k in 0..groups.len() {
        let g = groups[i].clone();
        let h = groups[j].clone();
        let k = groups[k].clone();
        handles.push(std::thread::spawn(move || {
          if g.cross_product(&k).is_isomorphic(&h.cross_product(&k)) {
            println!("{:?}", g);
            println!("{:?}", h);
            println!("{:?}", k);
          }
        }));
      }
    }
  }

  println!("{}", handles.len());
  while let Some(h) = handles.pop() {
    h.join().unwrap();
  }
}
