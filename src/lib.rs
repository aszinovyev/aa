extern crate multiarray;

pub mod aa {
  use multiarray::Array2D;

  pub struct Permutation {
    stack: Vec<u32>,
    arr: Box<[u32]>,
  }

  impl Permutation {
    pub fn new(n: u32) -> Permutation {
      Permutation {
        stack: Vec::with_capacity(n as usize),
        arr: (0..n).collect::<Vec<_>>().into_boxed_slice(),
      }
    }

    pub fn get(&self) -> &[u32] {
      &self.arr[0..self.stack.len()]
    }

    pub fn next(&mut self) {
      let n = self.arr.len();
      let m = self.stack.len();

      if m == n {
        self.stepover();
      } else {
        self.stack.push(m as u32);
      }
    }

    pub fn stepover(&mut self) {
      self.unwind();
      if !self.stack.is_empty() {
        self.swap();
        *self.stack.last_mut().unwrap() += 1;
        self.swap();
      }
    }

    fn swap(&mut self) {
      self.arr.swap(self.stack.len() - 1, *self.stack.last().unwrap() as usize);
    }

    fn unwind(&mut self) {
      while (!self.stack.is_empty()) && 
            (*self.stack.last().unwrap() == ((self.arr.len() - 1) as u32)) {
        self.swap();
        self.stack.pop();
      }
    }
  }

  #[derive(Clone, Debug, PartialEq, Eq)]
  pub struct Group {
    // Size of the group minus 1.
    len: u32,
    // Size is len^2. Contains elements in [0..len). len denotes the identity.
    cayley: Box<[u32]>,
  }

  impl Group {
    pub fn new(size: u32, cayley: Box<[u32]>) -> Group {
      let len = size - 1;
      assert_eq!((len as usize) * (len as usize), cayley.len());

      let res = Group {
        len,
        cayley,
      };

      for i in 0..len {
        for j in 0..len {
          assert!(res.get(i, j) <= len);
          assert_eq!(res.get(i, j) == res.id(), res.get(j, i) == res.id());
        }
      }

      for i in 0..len {
        assert!(Self::is_id_in_row(&res, i));
      }
      for j in 0..len {
        assert!(Self::is_id_in_column(&res, j));
      }

      assert!(Self::satisfies_transitivity(&res));

      res
    }

    pub fn with_size(size: u32) -> Vec<Group> {
      if size == 0 {
        Vec::new()
      } else if size == 1 {
        vec![Group{len: 0, cayley: Box::new([])}]
      } else {
        let len = size - 1;

        let mut g = Group {
          len,
          cayley: vec![0; (len as usize) * (len as usize)].into_boxed_slice(),
        };

        let mut used_in_columns = 
            Array2D::new([len as usize, size as usize], false);
        for i in 0..(len as usize) {
          used_in_columns[[i, i]] = true;
        }
        let mut used_in_rows = 
            Array2D::new([len as usize, size as usize], false);
        for j in 0..(len as usize) {
          used_in_rows[[j, j]] = true;
        }

        let mut seen = vec![false; len as usize].into_boxed_slice();

        let mut res = Vec::new();
        Self::with_size_rec(&mut g, 0, 0, &mut used_in_columns,
                            &mut used_in_rows, &mut seen, &mut res);

        return res;
      }
    }

    pub fn id(&self) -> u32 {
      self.len
    }

    pub fn size(&self) -> u32 {
      self.len + 1
    }

    // Product of y and x.
    pub fn op(&self, y: u32, x: u32) -> u32 {
      if y == self.id() {
        x
      } else if x == self.id() {
        y
      } else {
        self.get(y, x)
      }
    }

    pub fn is_isomorphic(&self, other: &Group) -> bool {
      if other.len != self.len {
        false
      } else {
        let mut perm = Permutation::new(self.len);
        perm.next();

        while perm.get() != [] {
          if self.can_be_isomorphism(other, &perm) {
            if perm.get().len() == (self.len as usize) {
              return true;
            } else {
              perm.next();
            }
          } else {
            perm.stepover();
          }
        }

        false
      }
    }

    fn is_id_in_row(g: &Group, y: u32) -> bool {
      for j in 0..g.len {
        if g.get(y, j) == g.id() {
          return true;
        }
      }
      false
    }

    fn is_id_in_column(g: &Group, x: u32) -> bool {
      for i in 0..g.len {
        if g.get(i, x) == g.id() {
          return true;
        }
      }
      false
    }

    fn satisfies_transitivity(g: &Group) -> bool {
      for i in 0..g.len {
        for j in 0..g.len {
          for k in 0..g.len {
            if g.op(g.op(i, j), k) != g.op(i, g.op(j, k)) {
              return false;
            }
          }
        }
      }
      true
    }

    // Returns false iff `g` is isomorphic to some group in `groups`.
    fn is_unique(g: &Group, groups: &[Group]) -> bool {
      for gg in groups {
        if g.is_isomorphic(gg) {
          return false;
        }
      }
      true
    }

    fn with_size_rec_try(g: &mut Group, y: u32, x: u32, v: u32, 
                         used_in_columns: &mut Array2D<bool>,
                         used_in_rows: &mut Array2D<bool>,
                         seen: &mut Box<[bool]>,
                         append_to: &mut Vec<Group>) {
      g.set(y, x, v);
      used_in_columns[[y as usize, v as usize]] = true;
      used_in_rows[[x as usize, v as usize]] = true;
      let mut was_seen = false;
      if v != g.len {
        was_seen = seen[v as usize];
        seen[v as usize] = true;
      }

      if (y == g.len - 1) && (x == g.len - 1) {
        if Self::satisfies_transitivity(g) && Self::is_unique(g, append_to) {
          append_to.push(g.clone());
        }
      } else {
        let mut yn = y;
        let mut xn = x + 1;
        if xn == g.len {
          yn += 1;
          xn = 0;
        }
        Self::with_size_rec(g, yn, xn, used_in_columns, used_in_rows, seen,
                            append_to);
      }

      used_in_columns[[y as usize, v as usize]] = false;
      used_in_rows[[x as usize, v as usize]] = false;
      if v != g.len {
        seen[v as usize] = was_seen;
      }
    }

    fn with_size_rec(g: &mut Group, y: u32, x: u32, 
                     used_in_columns: &mut Array2D<bool>,
                     used_in_rows: &mut Array2D<bool>,
                     seen: &mut Box<[bool]>,
                     append_to: &mut Vec<Group>) {
      let id = g.id();
      if (y <= x) || (g.op(x, y) != id) {
        let mut tried_unseen = false;
        for v in 0..g.len {
          if !used_in_columns[[y as usize, v as usize]] &&
             !used_in_rows[[x as usize, v as usize]] &&
             (!tried_unseen || seen[v as usize]) {
            if !seen[v as usize] {
              tried_unseen = true;
            }
            Self::with_size_rec_try(g, y, x, v, used_in_columns, used_in_rows,
                                    seen, append_to);
          }
        }
      }
      if ((y <= x) || (g.op(x, y) == id)) &&
         !used_in_columns[[y as usize, id as usize]] &&
         !used_in_rows[[x as usize, id as usize]] {
        Self::with_size_rec_try(g, y, x, id, used_in_columns, used_in_rows, 
                                seen, append_to);
      }
    }

    fn index(&self, y: u32, x: u32) -> usize {
      (y * self.len + x) as usize
    }

    fn get(&self, y: u32, x: u32) -> u32 {
      self.cayley[self.index(y, x)]
    }

    fn set(&mut self, y: u32, x: u32, v: u32) {
      self.cayley[self.index(y, x)] = v
    }

    fn can_be_isomorphism(&self, other: &Group, perm: &Permutation) -> bool {
      for i in 0..perm.get().len() {
        for j in 0..perm.get().len() {
          let ij = self.op(i as u32, j as u32);  // product of i and j
          if (ij as usize) < perm.get().len() {
            if perm.get()[ij as usize] != other.op(perm.get()[i], perm.get()[j]) {
              return false;
            }
          }
        }
      }
      true
    }

    pub fn cross_product(&self, rhs: &Group) -> Group {
      let len = (self.len + 1) * (rhs.len + 1) - 1;
      let mut res = Group {
        len,
        cayley: vec![0; (len as usize) * (len as usize)].into_boxed_slice(),
      };

      let mut k0: u32 = 0;
      for g0 in 0..(self.len + 1) {
        for h0 in 0..(rhs.len + 1) {
          if k0 < len {
            let mut k1: u32 = 0;
            for g1 in 0..(self.len + 1) {
              for h1 in 0..(rhs.len + 1) {
                if k1 < len {
                  res.set(
                      k0, k1, self.op(g0, g1) * (rhs.len + 1) + rhs.op(h0, h1));
                  k1 += 1;
                }  // if k1
              }  // for h1
            }  // for g1
            k0 += 1;
          }  // if k0
        }  // for h0
      }  // for g0

      res
    }
  }
}

#[cfg(test)]
mod permutation_tests {
  use super::aa::Permutation;

  #[test]
  fn len_0_init() {
    let p = Permutation::new(0);
    assert_eq!(p.get(), []);
  }
  #[test]
  fn len_0_next() {
    let mut p = Permutation::new(0);
    p.next();
    assert_eq!(p.get(), []);
  }
  #[test]
  fn len_0_stepover() {
    let mut p = Permutation::new(0);
    p.stepover();
    assert_eq!(p.get(), []);
  }
  #[test]
  fn init() {
    let p = Permutation::new(0);
    assert_eq!(p.get(), []);
  }
  #[test]
  fn next_steps_inside() {
    let mut p = Permutation::new(3);
    p.next();
    assert_eq!(p.get(), [0]);
    p.next();
    assert_eq!(p.get(), [0, 1]);
  }
  #[test]
  fn next_after_full() {
    let mut p = Permutation::new(3);
    p.next();
    p.next();
    p.next();
    p.next();
    assert_eq!(p.get(), [0, 2]);
  }
  #[test]
  fn next_after_last() {
    let mut p = Permutation::new(2);
    p.next();
    p.next();
    p.next();
    p.next();
    p.next();
    assert_eq!(p.get(), []);
  }
  #[test]
  fn stepover_after_last() {
    let mut p = Permutation::new(2);
    p.next();
    p.next();
    p.next();
    p.next();
    p.stepover();
    assert_eq!(p.get(), []);
  }
  #[test]
  fn stepover_then_next() {
    let mut p = Permutation::new(3);
    p.next();
    assert_eq!(p.get(), [0]);
    p.stepover();
    assert_eq!(p.get(), [1]);
    p.next();
    assert_eq!(p.get(), [1, 0]);
  }
  #[test]
  fn stepover_after_full() {
    let mut p = Permutation::new(3);
    p.next();
    p.next();
    p.next();
    p.stepover();
    assert_eq!(p.get(), [0, 2]);
  }
  #[test]
  fn stepover_after_empty() {
    let mut p = Permutation::new(3);
    p.stepover();
    assert_eq!(p.get(), []);
  }
  #[test]
  fn stepover_until_empty() {
    let mut p = Permutation::new(3);
    p.next();  // [0]
    p.next();  // [0, 1]
    p.stepover();  // [0, 2]
    p.stepover();  // [1]
    p.stepover();  // [2]
    p.stepover();  // []
  }
}

#[cfg(test)]
mod group_tests {
  use super::aa::Group;

  fn z(n: u32) -> Group {
    let len = n - 1;
    let mut cayley = vec![0; (len * len) as usize].into_boxed_slice();
    let mut k = 0;
    for i in 0..len {
      for j in 0..len {
        cayley[k] = (i + 1 + j) % n;
        k += 1;
      }
    }
    Group::new(n, cayley)
  }

  // p and q are elements of D(n). If p < n, it denotes R^p, where R is rotation
  // to the left by 1. If n <= p < n, p denotes FR^p, where F is reflection.
  fn d_op(n: u32, p: u32, q: u32) -> u32 {
    if p < n {
      if q < n {
        (p + q) % n
      } else {
        n + (q - p) % n
      }
    } else {
      if q < n {
        n + (p + q) % n
      } else {
        (n + q - p) % n
      }
    }
  }

  fn d(n: u32) -> Group {
    let len = 2*n - 1;
    let mut cayley = 
        vec![0; (len * len) as usize].into_boxed_slice();
    let mut k = 0;
    for i in 0..len {
      for j in 0..len {
        cayley[k] = (2*n + d_op(n, i + 1, j + 1) - 1) % (2*n);
        k += 1;
      }
    }
    Group::new(2*n, cayley)
  }

  #[test]
  fn with_size_0() {
    let groups = Group::with_size(0);
    assert_eq!(0, groups.len());
  }

  #[test]
  fn with_size_1() {
    let groups = Group::with_size(1);
    assert_eq!(1, groups.len());
    assert_eq!(z(1), groups[0]);
  }

  #[test]
  fn with_size_2() {
    let groups = Group::with_size(2);
    assert_eq!(1, groups.len());
    assert_eq!(z(2), groups[0]);
  }

  #[test]
  fn with_size_3() {
    let groups = Group::with_size(3);
    assert_eq!(1, groups.len());
    assert_eq!(z(3), groups[0]);
  }

  #[test]
  fn with_size_4() {
    let groups = Group::with_size(4);
    assert_eq!(2, groups.len());

    let u_8 = [1, 7, 5,
               7, 1, 3,
               5, 3, 1];
    let u_8 = Group::new(4, u_8.iter()
        .map(|&x| match x {1 => 3, 3 => 0, 5 => 1, 7 => 2, _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());

    assert!((groups[0].is_isomorphic(&z(4)) && groups[1].is_isomorphic(&u_8)) ||
            (groups[1].is_isomorphic(&z(4)) && groups[0].is_isomorphic(&u_8)));
  }

  // Did not verify by hand, but it should help find regressions.
  #[test]
  fn with_size_5() {
    let groups = Group::with_size(5);
    assert_eq!(1, groups.len());
    assert_eq!(z(5), groups[0]);
  }

  // Did not verify by hand, but it should help find regressions.
  #[test]
  fn with_size_6() {
    let groups = Group::with_size(6);
    assert_eq!(2, groups.len());
    assert!((groups[0].is_isomorphic(&z(6)) && groups[1].is_isomorphic(&d(3))) ||
            (groups[1].is_isomorphic(&z(6)) && groups[0].is_isomorphic(&d(3))));
  }

  #[test]
  fn is_isomorphic_diff_size() {
    assert!(!z(2).is_isomorphic(&z(3)));
    assert!(!z(3).is_isomorphic(&z(2)));
  }

  #[test]
  fn is_isomorphic_yes() {
    let g0 = Group::new(4, Box::new([1, 2, 3, 2, 3, 0, 3, 0, 1]));  // Z_4
    // Isomorphism: 0 -> 1, 1 -> 2, 2 -> 0.
    let g1 = Group::new(4, Box::new([2, 3, 1, 3, 2, 0, 1, 0, 3]));  // Z_4
    assert!(g0.is_isomorphic(&g1));
    assert!(g1.is_isomorphic(&g0));
  }

  #[test]
  fn is_isomorphic_no() {
    let z_4 = Group::new(4, Box::new([1, 2, 3, 2, 3, 0, 3, 0, 1]));  // Z_4
    let u_8 = Group::new(4, Box::new([3, 2, 1, 2, 3, 0, 1, 0, 3]));  // U(8)
    assert!(!z_4.is_isomorphic(&u_8));
    assert!(!u_8.is_isomorphic(&z_4));
  }

  #[test]
  fn cross_product_z_1_d_3() {
    assert!(d(3).is_isomorphic(&d(3).cross_product(&z(1))));
    assert!(d(3).is_isomorphic(&z(1).cross_product(&d(3))));
  }

  #[test]
  fn cross_product_z_2_d_3() {
    assert!(d(6).is_isomorphic(&z(2).cross_product(&d(3))));
    assert!(d(6).is_isomorphic(&d(3).cross_product(&z(2))));
  }

  #[test]
  fn cross_product_z_2_z_3() {
    let g = z(2).cross_product(&z(3));
    let h = z(3).cross_product(&z(2));
    assert!(g.is_isomorphic(&h));
  }

  #[test]
  fn cross_product_z_2_z_5() {
    let g = z(2).cross_product(&z(5));
    let h = z(5).cross_product(&z(2));
    assert!(g.is_isomorphic(&h));
  }
}
