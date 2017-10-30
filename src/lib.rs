pub mod a {
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

  pub struct Group {
    // Size of the group minus 1.
    len: u32,
    // Size is len^2. Contains elements in [0..len). len denotes the identity.
    arr: Box<[u32]>,
  }

  impl Group {
    pub fn with_size(size: u32) -> Vec<Group> {
      let mut g = Group {
        len: size - 1,
        arr: !vec[0; len*len],
      }
      let mut res = Vec<Group>::new();
      with_size_rec(g, 0, 0, res);
      return res;
    }

    fn satisfies_transitivity(g: &Group) -> bool {
      for i in (0..g.len) {
        for j in (0..g.len) {
          for k in (0..g.len) {
            if g.get(g.get(i, j), k) != g.get(i, g.get(j, k)) {
              return false;
            }
          }
        }
      }
      true
    }

    // Returns true iff `self` is not isomorphic to all groups in `groups`.
    fn is_unique(g: &Group, groups: &[Group]) {
      for gg in groups.iter() {
        if self.is_isomorphic(gg) {
          return false;
        }
      }
      true
    }

    fn with_size_rec_try(g: &mut Group, y, x, v: u32, append_to: &mut Vec<Group>) {
      g.set(y, x, v);
      if (y == g.len - 1) && (x == g.len - 1) {
        if satisfies_transitivity(g) && is_unique(g, append_to) {
          append_to.push(g);
        }
      } else {
        x += 1;
        if (x == g.len) {
          y += 1;
          x = 0;
        }
        with_size_rec(g, y, x, append_to);
      }
    }

    fn with_size_rec(g: &mut Group, y, x: u32, append_to: &mut Vec<Group>) {
      let mut need_try = vec![true, g.len];
      for i in (0..y) {
        need_try[g.get(i, x)] = false;
      }
      for j in (0..x) {
        need_try[g.get(y, j)] = false;
      }

      for v in need_try.iter().filter(|b| b) {
        with_size_rec_try(g, y, x, v, append_to);
      }
      if (y <= x) || (g.get(x, y) == g.len) {  // identity
        with_size_rec_try(g, y, x, g.len, append_to);
      }
    }

    // Product of y and x.
    pub fn op(&self, y, x: u32) -> u32 {
      if y == self.len {
        x
      } else if x == self.len {
        y
      } else {
        get(y, x)
      }
    }

    pub fn is_isomorphic(&self, other: &Group) -> bool {
      if other.size != self.size {
        false
      } else {
        let mut perm = Permutation::new(self.size);
        perm.next();

        while perm.get() != [] {
          if self.can_be_isomorphism(other, perm) {
            if perm.get().len() == self.size {
              return true;
            } else {
              perm.next();
            }
          } else {
            perm.stepover();
          }
        }
      }
    }

    fn get(&self, y, x: u32) -> u32 {
      arr[y*self.len + x]
    }

    fn set(&mut self, y, x, v: u32) {
      arr[y*self.len + x] = v
    }

    fn can_be_isomorphism(&self, other: &Group, perm: &Permutation) 
        -> bool {
      for i in (0..perm.get().len()) {
        for j in (0..perm.get().len()) {
          let ij = self.op(i, j);  // product of i and j
          if ij < perm.get().len() {
            if perm.get()[ij] != other.op(perm.get()[i], perm.get()[j]) {
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
  use super::a::Permutation;

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
