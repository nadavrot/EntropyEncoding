use crate::{
    bitvector::Bitvector,
    utils::{num_bits, Histogram},
};

pub struct Simple<const ALPHABET: usize, const TABLESIZE: usize> {
    bitvector: Bitvector,
    /// This is the main encoder table.
    /// A table of [Symbol x State] (use the get_state accessor).
    encode_table: Vec<u32>,
    /// Maps symbol to the max state that can encode this symbol.
    max_state: Vec<u32>,
    /// This is the main decoder table.
    /// Maps each state to (next_state, sym)
    decode_table: Vec<(u32, u8)>,
}

impl<const ALPHABET: usize, const TABLESIZE: usize>
    Simple<ALPHABET, TABLESIZE>
{
    pub fn new() -> Simple<ALPHABET, TABLESIZE> {
        Simple::<ALPHABET, TABLESIZE> {
            bitvector: Bitvector::new(),
            encode_table: vec![0; ALPHABET * TABLESIZE],
            max_state: vec![0; ALPHABET],
            decode_table: vec![(0, 0); TABLESIZE * 2],
        }
    }

    // Initialize the encoder and create the encoder/decoder tables based on
    // sample input.
    pub fn from_data(&mut self, data: &[u8]) {
        let mut hist = Histogram::<ALPHABET>::from_data(data);
        hist.normalize(TABLESIZE);
        let norm_hist = hist.get_bins();
        let state_list = self.spread_symbols(norm_hist);
        self.create_tables(norm_hist, &state_list);
    }

    /// Spread the symbols using Yann's method, which is to randomly place the
    /// symbols around the array, minimizing the distance between symbols
    /// (not grouping them together).
    fn spread_symbols(&self, sym_occurences: &[u32]) -> Vec<u8> {
        let mut state_table: Vec<u8> = vec![0; TABLESIZE];
        // This is a large prime number.
        let step = 7919;
        let mut pos: usize = 0;

        for (sym, occ) in sym_occurences.iter().enumerate() {
            for _i in 0..*occ {
                state_table[pos % TABLESIZE] = sym as u8;
                pos += step;
            }
        }
        // The lowest common denominator of the table at the prime is 1,
        // so we know that the cycle size will be the size of the table.
        assert!(pos % TABLESIZE == 0);
        state_table
    }

    fn get_state(&mut self, sym: usize, state: usize) -> &mut u32 {
        assert!(sym < ALPHABET && state < TABLESIZE);
        &mut self.encode_table[state * ALPHABET + sym]
    }

    pub fn dump(&mut self) {
        for state in 0..TABLESIZE {
            print!("{:3})", state);
            for a in 0..ALPHABET {
                print!("{:3} ", *self.get_state(a as usize, state as usize));
            }
            println!();
        }
    }

    /// Creates the encode/decode tables. normalized_occurences is the
    /// normalized histogram that accumulates to the sum of the table.
    /// state_list maps the allocated spread states symbols.
    /// http://www.ezcodesample.com/abs/abs_article.html
    /// and
    /// http://cbloomrants.blogspot.com/2014/02/02-04-14-understanding-ans-6.html
    /// Reference: cbloom "make_tables1".
    pub fn create_tables(
        &mut self,
        normalized_occurences: &[u32; ALPHABET],
        state_list: &[u8],
    ) {
        assert_eq!(normalized_occurences.iter().sum::<u32>(), TABLESIZE as u32);
        assert!(state_list.len() == TABLESIZE, "Invalid table size");

        // The initial encoder state is [Fs ... 2Fs-1].
        for s in 0..ALPHABET {
            // Max state is the first state that we want to fill.
            self.max_state[s] = normalized_occurences[s] - 1;
        }

        for to_state in TABLESIZE..(2 * TABLESIZE) - 1 {
            // Map the state to the symbol:
            let sym = state_list[to_state - TABLESIZE];

            self.max_state[sym as usize] += 1;
            let from_state = self.max_state[sym as usize];

            // Set the encode table.
            let entry = self.get_state(sym as usize, from_state as usize);
            *entry = to_state as u32;

            assert_eq!(self.decode_table[to_state].0, 0);
            self.decode_table[to_state].0 = from_state;
            self.decode_table[to_state].1 = sym;
        }
    }

    /// Encode a string into the bitvector.
    pub fn encode_data(&mut self, payload: &[u8]) {
        let mut state: u32 = TABLESIZE as u32;
        for sym in payload.iter().rev() {
            self.encode_one_symbol(&mut state, *sym);
        }
        let val = state as usize - TABLESIZE;
        let table_log = num_bits(TABLESIZE as u32 - 1) as usize;
        self.bitvector.push_word(val as u64, table_log);
    }

    fn encode_one_symbol(&mut self, state: &mut u32, sym: u8) {
        Self::check_state(*state);
        assert!(ALPHABET > sym as usize, "Invalid symbol");

        let max_state = self.max_state[sym as usize];

        // Renormalize: bring the state back to the encodable range.
        while *state > max_state {
            let lowest_bit = *state & 0x1;
            *state /= 2;
            self.bitvector.push_word(lowest_bit as u64, 1);
        }

        *state = *self.get_state(sym as usize, *state as usize);
        Self::check_state(*state);
    }

    fn check_state(state: u32) {
        assert!(
            state as usize >= TABLESIZE && state as usize <= TABLESIZE * 2,
            "State is not in the valid range"
        );
    }

    fn decode_one_symbol(&mut self, offset: &mut usize, state: &mut u32) -> u8 {
        // Renormalize the state and bring it to the valid range.
        while TABLESIZE > *state as usize {
            *offset -= 1;
            let bit = self.bitvector.read_nth_bits(*offset, 1);
            *state <<= 1;
            *state |= bit as u32;
        }

        Self::check_state(*state);

        let sym = self.decode_table[*state as usize].1 as u8;
        *state = self.decode_table[*state as usize].0;
        sym
    }

    /// Read a string from the bitvector.
    pub fn decode_data(&mut self) -> Vec<u8> {
        let table_log = num_bits(TABLESIZE as u32 - 1) as usize;
        let mut offset = self.bitvector.len() - table_log;
        let mut state: u32 = TABLESIZE as u32
            + self.bitvector.read_nth_bits(offset, table_log) as u32;
        let mut res = Vec::new();
        while offset != 0 {
            let sym = self.decode_one_symbol(&mut offset, &mut state);
            if offset != 0 {
                res.push(sym);
            }
        }
        res
    }
}

#[test]
fn test_round_trip_simple_encoder() {
    let text =  "entropy encoding is typically the last stage of a compression algorithm";
    let input: Vec<u8> = text.as_bytes().to_vec();

    // Define an encoder with 8bit symbols, and 12bit states.
    let mut enc = Simple::<256, 4096>::new();
    // Initialize the encoder based on the statistical properties of the input.
    enc.from_data(&input);
    // Encode the test.
    enc.encode_data(&input);
    // Print the compressed binary representation.
    enc.bitvector.dump();
    // Decode the data.
    let out = enc.decode_data();

    println!("Decoded {:?}", out);
    println!("Input length = {}", 8 * input.len());
    println!("Compressed length = {}", enc.bitvector.len());
    assert_eq!(out, input);
}
