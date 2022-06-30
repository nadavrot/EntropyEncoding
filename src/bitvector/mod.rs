
pub struct Bitvector {
    /// Stores the payload of the bitvector.
    /// The bits are always packed to the right [xxxxx012345][xxxxxxx]    
    data: Vec<u64>,
    // Points to the next free bit (also size of bitvector).
    len: usize,
}

impl Bitvector {
    pub fn new() -> Bitvector {
        Bitvector {
            data: vec![0],
            len: 0,
        }
    }

    pub fn clear(&mut self) {
        self.len = 0;
        self.data = vec![0];
    }

    // Set all of the bits above \p keep to zero.
    fn clear_upper_bits(bits: u64, keep: usize) -> u64 {
        let amt: u32 = (64 - keep) as u32;
        let shl = bits.checked_shl(amt).unwrap_or(0);
        shl.checked_shr(amt).unwrap_or(0)
    }

    fn capacity(&self) -> usize {
        self.data.len() * 64
    }

    /// Ensure that the bit vector can hold at least \p num_bits bits.
    fn grow(&mut self, num_bits: usize) {
        let mut capacity = self.capacity();
        while capacity <= num_bits {
            self.data.push(0);
            capacity += 64;
        }
    }

    /// Push the lowest \p len bits from \p bits.
    pub fn push_word(&mut self, bits: u64, len: usize) {
        assert!(len > 0 && len <= 64);
        let bits = Self::clear_upper_bits(bits, len);

        self.grow(self.len() + len);
        let capacity = self.capacity();
        let avail = capacity - self.len;

        let curr_len = self.len();
        let avail_last_word = (avail - 1) % 64 + 1;

        let last_word_idx = curr_len / 64;
        let last = self.data.get_mut(last_word_idx).unwrap();

        // If we can fit the current request in the last word.
        if avail_last_word >= len {
            assert!(len == 64 || bits >> len == 0, "upper bits must be zero");
            *last = last.checked_shl(len as u32).unwrap_or(0);            
            *last |= bits;
            self.len += len;
            return;
        }

        // Fill the current word:
        let shift = avail_last_word;
        let first_bits = bits >> (len - shift);
        *last <<= shift;
        *last |= first_bits;

        // Add a new word that contains the lower bits.
        self.data[last_word_idx + 1] =
            Self::clear_upper_bits(bits, len - shift);
        self.len += len;
    }

    /// Remove \p len bits from \p bits.
    pub fn pop_word(&mut self, num_bits: usize) -> u64 {
        // This is the layout of the two consecutive words. We need to read a
        // window that may straddle both words.
        //[012345|6789ABCDEF][xxxxx|abcdef] ...
        //    ^.......................^
        //
        assert!(self.len >= num_bits, "popping too many bits");
        let avail_in_last_word = (self.len - 1) % 64 + 1;

        let offset = self.len - num_bits;
        let first_word_idx = offset / 64;

        // Read all of the bits from the last word:
        if avail_in_last_word >= num_bits {
            let word = self.data.get_mut(first_word_idx).unwrap();
            let val = *word;
            *word = word.checked_shr(num_bits as u32).unwrap_or(0);
            self.len -= num_bits;
            return Self::clear_upper_bits(val, num_bits);
        }

        // Handle the case where the return value is split between two words.
        let first_word = self.data.get(first_word_idx).unwrap();
        let next_word = self.data.get(first_word_idx + 1).unwrap();

        let bits_from_second_word = self.len % 64;
        let bits_from_first_word = num_bits - bits_from_second_word;
        let low = Self::clear_upper_bits(*next_word, bits_from_second_word);
        let high = first_word << bits_from_second_word;
        let res = low | high;

        // Zero out the area that we read.
        self.data[first_word_idx] >>= bits_from_first_word;
        self.data[first_word_idx + 1] = 0;
        self.len -= num_bits;
        Self::clear_upper_bits(res, num_bits)
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn dump(&self) {
        print!("{{");
        for elem in self.data.iter() {
            print!("{:b}, ", elem);
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

    assert_eq!(bv.len(), 0);
    bv.push_word(0b1101, 4);
    assert_eq!(bv.len(), 4);
    assert_eq!(bv.pop_word(1), 1);
    assert_eq!(bv.pop_word(1), 0);
    assert_eq!(bv.pop_word(1), 1);
    assert_eq!(bv.pop_word(1), 1);
    assert_eq!(bv.len(), 0);

    bv.push_word(0xffaa, 16);
    let lower = bv.pop_word(8);
    let upper = bv.pop_word(8);
    assert_eq!(lower, 0xaa);
    assert_eq!(upper, 0xff);
}

#[test]
fn test_pop() {
    let mut bv = Bitvector::new();
    // Push and pop a few pairs.
    for i in 0..1000 {
        bv.push_word(i % 3, 1);
        let val = (i * 713) as u64;
        // Push a full word.
        bv.push_word(val, 64);
        let val2 = bv.pop_word(64);
        assert_eq!(val, val2);
    }
    bv.dump();
}

#[test]
fn test_bitvector_bug() {
    let mut bv = Bitvector::new();

    let mut counter = 1;

    for i in 1..56 {
        // Start the check at different offset in the vector.
        bv.push_word(0x1, i);

        // Outer push.
        counter = (counter * 7) & 0xffffffff;
        bv.push_word(counter, 32);

        // Do an inner push and pop to dirty the upper bits.
        bv.push_word(0xaf, 8);
        let val = bv.pop_word(8);
        assert_eq!(0xaf, val);

        // Check the outer value.
        let popped = bv.pop_word(32);
        assert_eq!(counter & 0xffffffff, popped);
    }
}
