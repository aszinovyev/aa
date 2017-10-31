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
    arr: Box<[u32]>,
  }

  impl Group {
    pub fn singleton() -> Group {
      Group {
        len: 0,
        arr: Vec::new().into_boxed_slice(),
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

    pub fn new(size: u32, arr: Box<[u32]>) -> Group {
      let len = size - 1;
      assert_eq!((len as usize) * (len as usize), arr.len());

      let res = Group {
        len,
        arr,
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
        vec![Self::singleton()]
      } else {
        let len = size - 1;

        let mut g = Group {
          len,
          arr: vec![0; (len as usize) * (len as usize)].into_boxed_slice(),
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

        let mut res = Vec::new();
        Self::with_size_rec(&mut g, 0, 0, &mut used_in_columns, 
                            &mut used_in_rows, &mut res);

        return res;
      }
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
                         append_to: &mut Vec<Group>) {
      g.set(y, x, v);
      used_in_columns[[y as usize, v as usize]] = true;
      used_in_rows[[x as usize, v as usize]] = true;

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
        Self::with_size_rec(g, yn, xn, used_in_columns, used_in_rows, 
                            append_to);
      }

      used_in_columns[[y as usize, v as usize]] = false;
      used_in_rows[[x as usize, v as usize]] = false;
    }

    fn with_size_rec(g: &mut Group, y: u32, x: u32, 
                     used_in_columns: &mut Array2D<bool>,
                     used_in_rows: &mut Array2D<bool>,
                     append_to: &mut Vec<Group>) {
      let id = g.id();
      if (y <= x) || (g.op(x, y) != id) {
        for v in 0..g.len {
          if !used_in_columns[[y as usize, v as usize]] &&
             !used_in_rows[[x as usize, v as usize]] {
            Self::with_size_rec_try(g, y, x, v, used_in_columns, 
                                    used_in_rows, append_to);
          }
        }
      }
      if ((y <= x) || (g.op(x, y) == id)) &&
         !used_in_columns[[y as usize, id as usize]] &&
         !used_in_rows[[x as usize, id as usize]] {
        Self::with_size_rec_try(g, y, x, id, used_in_columns, 
                                used_in_rows, append_to);
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

    fn index(&self, y: u32, x: u32) -> usize {
      (y * self.len + x) as usize
    }

    fn get(&self, y: u32, x: u32) -> u32 {
      self.arr[self.index(y, x)]
    }

    fn set(&mut self, y: u32, x: u32, v: u32) {
      self.arr[self.index(y, x)] = v
    }

    fn can_be_isomorphism(&self, other: &Group, perm: &Permutation) 
        -> bool {
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

  #[test]
  fn singleton() {
    let g = Group::singleton();
    assert_eq!(1, g.size());
    assert_eq!(g.id(), g.op(g.id(), g.id()));
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
    assert_eq!(&Group::singleton(), &groups[0]);
  }

  #[test]
  fn with_size_2() {
    let groups = Group::with_size(2);
    assert_eq!(1, groups.len());
    let g = &groups[0];

    assert_eq!(2, g.size());
    assert_eq!(g.id(), g.op(g.id(), g.id()));
    assert_eq!(0, g.op(0, g.id()));
    assert_eq!(0, g.op(g.id(), 0));
    assert_eq!(g.id(), g.op(0, 0));
  }

  #[test]
  fn with_size_3() {
    let groups = Group::with_size(3);
    assert_eq!(1, groups.len());
    let g = &groups[0];

    let z_3 = [2, 0,
               0, 1];
    let z_3 = Group::new(3, z_3.iter()
        .map(|&x| match x {0 => 2, 1...2 => (x - 1), _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());
    assert!(g.is_isomorphic(&z_3));
  }

  #[test]
  fn with_size_4() {
    let groups = Group::with_size(4);
    assert_eq!(2, groups.len());

    let z_4 = [2, 3, 0,
               3, 0, 1,
               0, 1, 2];
    let z_4 = Group::new(4, z_4.iter()
        .map(|&x| match x {0 => 3, 1...3 => (x - 1), _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());
    let u_8 = [1, 7, 5,
               7, 1, 3,
               5, 3, 1];
    let u_8 = Group::new(4, u_8.iter()
        .map(|&x| match x {1 => 3, 3 => 0, 5 => 1, 7 => 2, _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());

    assert!((groups[0].is_isomorphic(&z_4) && groups[1].is_isomorphic(&u_8)) ||
            (groups[1].is_isomorphic(&z_4) && groups[0].is_isomorphic(&u_8)));
  }

  // Did not verify by hand, but it should help find regressions.
  #[test]
  fn with_size_5() {
    let groups = Group::with_size(5);
    assert_eq!(1, groups.len());
    let g = &groups[0];

    let z_5 = [2, 3, 4, 0,
               3, 4, 0, 1,
               4, 0, 1, 2,
               0, 1, 2, 3];
    let z_5 = Group::new(5, z_5.iter()
        .map(|&x| match x {0 => 4, 1...4 => (x - 1), _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());

    assert!(g.is_isomorphic(&z_5));
  }

  // Did not verify by hand, but it should help find regressions.
  #[test]
  fn with_size_6() {
    let groups = Group::with_size(6);
    assert_eq!(2, groups.len());

    let z_6 = [2, 3, 4, 5, 0, 
               3, 4, 5, 0, 1, 
               4, 5, 0, 1, 2,
               5, 0, 1, 2, 3,
               0, 1, 2, 3, 4];
    let z_6 = Group::new(6, z_6.iter()
        .map(|&x| match x {0 => 5, 1...5 => (x - 1), _ => panic!()})
        .collect::<Vec<u32>>().into_boxed_slice());
    let s_3 = Group::new(6, Box::new([1, 5, 4, 2, 3,
                                      5, 0, 3, 4, 2,
                                      3, 4, 5, 0, 1,
                                      4, 2, 1, 5, 0,
                                      2, 3, 0, 1, 5]));

    assert!((groups[0].is_isomorphic(&z_6) && groups[1].is_isomorphic(&s_3)) ||
            (groups[1].is_isomorphic(&z_6) && groups[0].is_isomorphic(&s_3)));
  }

  #[test]
  fn is_isomorphic_diff_size() {
    let g0 = Group::singleton();
    let g1 = Group::new(2, Box::new([1]));
    assert!(!g0.is_isomorphic(&g1));
    assert!(!g1.is_isomorphic(&g0));
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
}
