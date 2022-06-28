pub struct Bitvector {
    /// Stores the payload of the bitvector.
    /// The bits are always packed to the left [012345xxxxxx][xxxxxxx][xxxxxx]
    data: Vec<u64>,
    // Points to the next free bit (also size of bitvector).
    len: usize,
}

impl Bitvector {
    pub fn new() -> Bitvector {
        Bitvector {
            // Init with at least one value to overcome edge case in 'push'.
            data: vec![0],
            len: 0,
        }
    }

    pub fn clear(&mut self) {
        self.len = 0;
        self.data = vec![0];
    }

    pub fn push(&mut self, bit: bool) {
        if self.len >= self.data.len() * 64 {
            self.data.push(0);
        }

        let last = self.data.last_mut().unwrap();
        let shift = self.len % 64;
        let mask = (bit as u64) << (63 - shift);
        *last |= mask;
        self.len += 1;
    }

    // Set all of the bits above \p keep to zero.
    fn clear_upper_bits(bits: u64, keep: usize) -> u64 {
        if keep >= 64 {
            return bits;
        }
        let shl = bits << (64 - keep);
        shl >> (64 - keep)
    }

    /// Store \p len bits from \p bits.     
    pub fn push_word(&mut self, bits: u64, len: usize) {
        if self.len >= self.data.len() * 64 {
            self.data.push(0);
        }

        assert!(len > 0);
        let bits = Self::clear_upper_bits(bits, len);

        assert!(len <= 64, "Saving too many bits");
        let capacity = self.data.len() * 64;
        assert!(capacity >= self.len, "invalid capacity");
        let avail = capacity - self.len;

        let last = self.data.last_mut().unwrap();

        // If we can fit the current request in the last word.
        if avail >= len {
            //assert!(bits >> len == 0, "upper bits must be zero");
            let shift = avail - len;
            *last |= bits << shift;
            self.len += len;
            return;
        }

        // Fill the current word:
        let first_bits = bits >> (len - avail);
        *last |= first_bits;

        // Add a new word that contains the lower bits.
        self.data.push(bits << (64 - (len - avail)));
        self.len += len;
    }

    pub fn nth(&self, n: usize) -> bool {
        assert!(n < self.len, "Invalid bit");
        let word = self.data.get(n / 64).unwrap();
        let shift = 63 - (n % 64);
        ((word >> shift) & 0x1) != 0
    }

    pub fn read_nth_bits(&self, n: usize, bits: usize) -> u64 {
        // This is the layout of the two consecutive words. We need to read
        // a window that may straddle both words.
        //[01234567...][abcdef....]
        //    ^...........^
        //
        assert!(n + bits <= self.len, "Invalid bit");
        let first_bit_idx = n % 64;
        let avail_bits = 64 - first_bit_idx;

        // If we can read everything from the current word then return it.
        if avail_bits >= bits {
            let first_word = self.data.get(n / 64).unwrap();
            let first_bit = n % 64;
            let shifted = *first_word >> (64 - (first_bit + bits));
            return Self::clear_upper_bits(shifted, bits);
        }

        // Copy the bits from the current word.

        let first_word = self.data.get(n / 64).unwrap();
        let next_word = self.data.get((n / 64) + 1).unwrap();

        let a = first_word << first_bit_idx;
        let b = next_word >> avail_bits;
        let c = a | b;
        c >> (64 - bits)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn dump(&self) {
        print!("[");
        for i in 0..self.len {
            print!("{}", self.nth(i) as usize);
            if i % 32 == 31 {
                print!("\n.");
            }
        }
        println!("]");

        print!("{{");
        for elem in self.data.iter() {
            print!("{:08x}, ", elem);
        }
        println!("}}");
    }
}

#[test]
fn test_clear_upper() {
    assert_eq!(Bitvector::clear_upper_bits(0x3, 1), 1);
    assert_eq!(Bitvector::clear_upper_bits(0x3, 2), 3);
    assert_eq!(Bitvector::clear_upper_bits(0x3, 3), 3);
    assert_eq!(Bitvector::clear_upper_bits(0xffff, 8), 255);
}

#[test]
fn test_bitvector_simple() {
    let mut bv = Bitvector::new();
    // Check that the size of the bitvector changes as we insert values.
    assert_eq!(bv.len(), 0);
    bv.push(true);
    assert_eq!(bv.len(), 1);
    bv.push(false);
    assert_eq!(bv.len(), 2);
    assert_eq!(bv.nth(0), true);
    assert_eq!(bv.nth(1), false);
}

#[test]
fn test_bitvector_push0() {
    let mut bv = Bitvector::new();

    // Test vector 0
    bv.push_word(0x0, 32);
    bv.push_word(0xff, 8);
    let v2 = bv.read_nth_bits(32, 8);
    assert_eq!(v2, 255);
    bv.clear();

    // Test vector 1
    bv.push_word(0xff, 8);
    let v2 = bv.read_nth_bits(0, 8);
    assert_eq!(v2, 255);
    bv.clear();

    // Test vector 2
    bv.push_word(0x0, 2);
    let val = Bitvector::clear_upper_bits(0xffffffffffffffff, 63);
    bv.push_word(val, 63);
    let v2 = bv.read_nth_bits(2, 63);
    assert_eq!(val, v2);

    // Test vector 3
    bv.push_word(0x0, 62);
    let idx = bv.len();
    let val = Bitvector::clear_upper_bits(0x1037, 10);
    bv.push_word(val, 10);
    let v2 = bv.read_nth_bits(idx, 10);
    assert_eq!(val, v2);

    // Test a bunch of different sizes and offsets.
    for size in 1..64 {
        for offset in 1..64 {
            bv.push_word(0x0, offset);
            let idx = bv.len();
            let val = Bitvector::clear_upper_bits(0xffffffffff1f4f0f, size);
            bv.push_word(val, size);
            let v2 = bv.read_nth_bits(idx, size);
            assert_eq!(val, v2);
        }
    }
}

#[test]
fn test_bitvector_push1() {
    fn pack_bits(bits: &[u8]) -> u64 {
        let mut ret: u64 = 0;
        for elem in bits.iter() {
            ret <<= 1;
            if *elem != 0 {
                ret += 1;
            }
        }
        ret
    }

    let mut bv = Bitvector::new();

    let bits = pack_bits(&[0, 1, 1]);
    bv.push_word(bits, 3);
    assert_eq!(bv.read_nth_bits(0, 3), bits);
    bv.dump();
    assert_eq!(bv.len(), 3);
    assert_eq!(bv.nth(0), false);
    assert_eq!(bv.nth(1), true);
    assert_eq!(bv.nth(2), true);

    bv.push_word(0x0, 64);
    assert_eq!(bv.nth(64 + 0), false);
    assert_eq!(bv.nth(64 + 1), false);
    assert_eq!(bv.nth(64 + 2), false);

    bv.push_word(0x1, 1);
    assert_eq!(bv.nth(64 + 3), true);
    bv.dump();

    // Push a bunch of values.
    for _ in 0..10 {
        for word_size in 1..64 {
            let val = 0x1412 * word_size as u64;
            let val = Bitvector::clear_upper_bits(val, word_size);
            let idx = bv.len();
            bv.push_word(val, word_size);
            let val2 = bv.read_nth_bits(idx, word_size);
            assert_eq!(val2, val);
        }
    }
}

#[test]
fn test_bitvector_bug() {
    let mut bv = Bitvector::new();
    bv.push_word(0b0, 1);
    bv.push_word(0b0, 1);
    bv.push_word(0b1, 2);
    bv.dump();
}
