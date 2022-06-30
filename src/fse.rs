use crate::{
    bitvector::Bitvector,
    utils::{num_bits, Histogram},
};

#[derive(Clone, Copy, Debug, PartialEq, Default)]
pub struct SymbolTransform {
    /// See http://fastcompression.blogspot.com/2014/02/fse-encoding-how-it-works.html
    /// http://fastcompression.blogspot.com/2014/02/fse-encoding-part-2.html
    /// Offset to the next state after encoding a symbol (deltaFindState).
    delta_state: i32,
    /// The highest state that the current state can reach (maxState).
    max_state: u32,
    /// The number of bits needed to encode the symbol (minBitsOut).
    num_bits: u32,
}
impl SymbolTransform {
    pub fn from(
        delta_state: i32,
        max_state: u32,
        num_bits: u32,
    ) -> SymbolTransform {
        SymbolTransform {
            delta_state,
            max_state,
            num_bits,
        }
    }
}

/// This is a row in the decoer table.
/// See http://fastcompression.blogspot.com/2014/02/fse-encoding-how-it-works.html
/// Also check out 'decode_one_symbols'.
#[derive(Debug)]
pub struct DecoderEntry {
    /// The symbol that was decoded.
    symbol: u32,
    /// the number of bits that we need to read next.
    num_bits: u32,
    /// The next state that we jump into.
    new_state: u32,
}

type SymbolTransformTable = Vec<SymbolTransform>;
type CodingTable = Vec<u32>;
type DecodingTable = Vec<DecoderEntry>;

/// Stores the list of ranges that span the state table. This is done by
/// integrating the normalized symbol occurences table.
/// To understand this part you will need to read this:
/// http://fastcompression.blogspot.com/2014/02/fse-tricks-memory-efficient-subrange.html
type RangeList = Vec<u32>;

/// Maps a location in the encoding/decoding table into the symbol index.
type EncIdxToSymbol = Vec<u32>;

/// A simple implementation of the FSE encoder/decoder algorithm. This
/// implementation omits some of the details of normalization and skips some of
/// the edge cases of uniform arrays, and sparse inputs.
pub struct FSE {
    /// The data is serialized and read from this bitvector.
    bitvector: Bitvector,
    /// This is the size of the table (in log2).
    table_log: usize,
}

impl FSE {
    pub fn new(table_log: usize) -> FSE {
        FSE {
            bitvector: Bitvector::new(),
            table_log,
        }
    }

    pub fn get_table_size(&self) -> usize {
        1 << self.table_log
    }
}

impl FSE {
    /// Generate the state list (accumulated occurences) for the normalized
    /// symbol occurences table for a given table size.
    /// Reference: FSE_buildCTable_wksp
    /// http://fastcompression.blogspot.com/2014/02/fse-distributing-symbol-values.html
    /// [0..256 - 'a',   256 .. 512 'b', 512 .. 1024 - 'c']
    pub fn generate_range_list(&self, sym_occurences: &[u32]) -> RangeList {
        assert!(
            sym_occurences.iter().sum::<u32>() as usize
                == self.get_table_size()
        );

        // Symbol start positions:
        let len = sym_occurences.len();
        let mut cumulative = vec![0; len + 2];
        for i in 1..len + 1 {
            cumulative[i] = cumulative[i - 1] + sym_occurences[i - 1]
        }
        cumulative[len + 1] = (self.get_table_size() + 1) as u32;
        cumulative
    }

    /// Generate the state_table (spread the numbers semi-randomly).
    /// Reference: FSE_buildCTable_wksp
    /// Visualized in the picture here:
    /// http://fastcompression.blogspot.com/2014/02/fse-distributing-symbol-values.html
    pub fn generate_state_table(
        &self,
        sym_occurences: &[u32],
    ) -> EncIdxToSymbol {
        let mut state_table: Vec<u32> = vec![0; self.get_table_size()];
        let table_size = self.get_table_size() as u32;
        let high_thresh = table_size - 1;
        let table_mask = table_size - 1;
        // This kind of looks like a prime number, so the LCD of the table size
        // and the step is 1, so we know that the cycle will be equal to the
        // table size and we won't step on the same element twice.
        // This gives the effect of shuffling the elements around.
        let step = (table_size >> 1) + (table_size >> 3) + 3;
        let mut pos: u32 = 0;

        // Spread symbols:
        for (sym, occ) in sym_occurences.iter().enumerate() {
            for _i in 0..*occ {
                state_table[pos as usize] = sym as u32;
                pos = (pos + step) & table_mask;
                while pos > high_thresh {
                    pos = (pos + step) & table_mask
                }
            }
        }
        assert!(pos == 0);
        state_table
    }

    /// Returns the decode table in the format (state, num_bits, new_state);
    /// Reference: FSE_buildDTable
    pub fn generate_decoding_table(
        &self,
        sym_occurences: &[u32],
        state_table: &[u32],
    ) -> DecodingTable {
        let mut decode_table = Vec::new();
        let mut occurences = sym_occurences.to_vec();
        for i in 0..self.get_table_size() {
            // Maps a location in the encoding/decoding table into the symbol index.
            let symbol = state_table[i];
            // The normalized occurences of the symbol.
            let x = occurences[symbol as usize];
            // Just like with the encoding table, we update the occurences to
            // fill a range (few states that grow from say 10..20, which is the
            // accumulation of the next value).
            occurences[symbol as usize] += 1;
            // X is the number of the normalized occurences of some symbol.
            // I think that we are subtracting from table_log because we are
            // trying to make sure that the state is table_log bits long, and we
            // figure out how many bits we need.
            let num_bits = self.table_log as u32 - (num_bits(x) - 1);
            let new_state = (x << num_bits) - self.get_table_size() as u32;
            let dec = DecoderEntry {
                symbol,
                num_bits,
                new_state,
            };
            decode_table.push(dec);
        }
        decode_table
    }

    /// Build the symbol transformation table.
    /// Returns an array with (SymbolTransform) for each state.
    /// Reference: FSE_buildCTable_wksp
    pub fn generate_symbol_transformation_table(
        &self,
        input_histogram: &[u32],
    ) -> SymbolTransformTable {
        // The symbol transform table.
        let mut sym_tt =
            vec![SymbolTransform::default(); input_histogram.len()];
        let mut total: i32 = 0;
        let table_log = self.table_log as u32;
        for s in 0..sym_tt.len() {
            let occurrences = input_histogram[s];
            assert!(occurrences != 0, "Expected a non-zero normalized value");

            sym_tt[s].num_bits = table_log - num_bits(occurrences - 1);
            sym_tt[s].delta_state = total - occurrences as i32;
            sym_tt[s].max_state = (occurrences << (sym_tt[s].num_bits + 1)) - 1;
            total += occurrences as i32;
        }

        sym_tt
    }

    /// Build the coding table:
    /// Reference: FSE_buildCTable_wksp
    /// Visualized in here: http://www.ezcodesample.com/abs/abs_article.html
    /// The returned coding table maps the current state into the next state.
    pub fn generate_coding_table(
        &self,
        range_list: &mut RangeList,
        state_table: &[u32],
    ) -> CodingTable {
        let mut coding_table: CodingTable = vec![0; self.get_table_size()];
        // Build table:
        for i in 0..self.get_table_size() {
            let s = state_table[i as usize];
            let t = &mut range_list[s as usize];
            coding_table[*t as usize] = (self.get_table_size() + i) as u32;
            // Move to the next cell within the region that's defined by the
            // accumulated values [0, 10, 20]. This becomes [6, ...] [7, ....]
            // until the value is incremented to fill the range [9 , ...].
            // This is how the coding table is filled with the rules in the link
            // above.
            *t += 1;
        }

        coding_table
    }
} // impl

// Implementation of the serialization methods
impl FSE {
    /// Encode one symbol and return the new state.
    /// Reference: FSE_encodeSymbol
    pub fn encode_one_symbols(
        &mut self,
        symbol: u8,
        state: u32,
        coding_tabel: &[u32],
        symbol_transform_table: &SymbolTransformTable,
    ) -> u32 {
        let symtt = symbol_transform_table[symbol as usize];
        let mut num_bits = symtt.num_bits;
        if state > symtt.max_state {
            num_bits += 1;
        }

        self.bitvector.push_word(state as u64, num_bits as usize);
        // Maps the current state to the new state.
        coding_tabel[((state >> num_bits) as i32 + symtt.delta_state) as usize]
    }

    /// Encode one symbol and return the new state.
    /// Reference: FSE_encodeSymbol
    pub fn decode_one_symbols(
        &mut self,
        state: &mut u32,
        decode_table: &DecodingTable,
    ) -> u8 {
        let sym = decode_table[*state as usize].symbol as u8;
        let nbits = decode_table[*state as usize].num_bits;
        let rest = self.bitvector.pop_word(nbits as usize); //self.bitvector.read_nth_bits(*offset, nbits as usize);
        *state = decode_table[*state as usize].new_state + rest as u32;
        sym
    }

    pub fn decode_data(&mut self, decode_table: &DecodingTable) -> Vec<u8> {
        let mut output = Vec::new();
        let mut state = self.bitvector.pop_word(self.table_log as usize) as u32;
        //self.bitvector.read_nth_bits(offset, self.table_log) as u32;

        while self.bitvector.len() != 0 {
            let sym = self.decode_one_symbols(&mut state, decode_table);
            output.push(sym);
        }

        output
    }

    pub fn encode_data(
        &mut self,
        symbols: &[u8],
        coding_tabel: &[u32],
        symbol_transform_table: &SymbolTransformTable,
    ) -> u32 {
        let mut state = self.encode_one_symbols(
            symbols[0],
            0,
            coding_tabel,
            symbol_transform_table,
        );
        self.bitvector.clear();
        for sym in symbols.iter().rev() {
            state = self.encode_one_symbols(
                *sym,
                state,
                coding_tabel,
                symbol_transform_table,
            );
        }
        let val = state as usize - self.get_table_size();
        self.bitvector.push_word(val as u64, self.table_log);
        state
    }
}

#[test]
fn test_normalize() {
    use crate::utils::normalize_to_total_sum;

    {
        let fse = FSE::new(6);
        let mut input: Vec<u32> = vec![10, 10, 12];
        let expect: Vec<u32> = vec![0, 20, 40, 64, 65];
        normalize_to_total_sum(&mut input, fse.get_table_size() as u32);
        println!("{:?}", input);
        let state_list = fse.generate_range_list(&input);
        println!("{:?}", state_list);
        assert_eq!(state_list, expect);
    }

    {
        let fse = FSE::new(5);
        let mut input: Vec<u32> = vec![10, 10, 12];
        let expect: Vec<u32> = vec![0, 10, 20, 32, 33];
        normalize_to_total_sum(&mut input, fse.get_table_size() as u32);
        println!("{:?}", input);
        let state_list = fse.generate_range_list(&input);
        println!("{:?}", state_list);
        assert_eq!(state_list, expect);
    }
}

#[test]
fn test_gen_state_table() {
    use crate::utils::normalize_to_total_sum;

    {
        let fse = FSE::new(5);
        let mut input: Vec<u32> = vec![10, 10, 12];
        let expect: Vec<u32> = vec![
            0, 0, 1, 2, 2, 0, 1, 1, 2, 2, 0, 1, 2, 2, 0, 0, 1, 2, 2, 0, 1, 1,
            2, 0, 0, 1, 2, 2, 0, 1, 1, 2,
        ];
        normalize_to_total_sum(&mut input, fse.get_table_size() as u32);
        println!("{:?}", input);
        let state_list = fse.generate_state_table(&input);
        println!("{:?}", state_list);
        assert_eq!(state_list, expect);
    }
}

#[test]
fn test_gen_sym_trans_table() {
    use crate::utils::normalize_to_total_sum;
    {
        let fse = FSE::new(5);
        let mut input: Vec<u32> = vec![10, 10, 12];
        let expect: SymbolTransformTable = vec![
            SymbolTransform::from(-10, 39, 1),
            SymbolTransform::from(0, 39, 1),
            SymbolTransform::from(8, 47, 1),
        ];
        normalize_to_total_sum(&mut input, fse.get_table_size() as u32);
        println!("{:?}", input);
        let stt = fse.generate_symbol_transformation_table(&input);
        print!("stt = {:?}", stt);
        assert_eq!(stt, expect);
    }
}

#[test]
fn test_encode_short_string() {
    use crate::utils::normalize_to_total_sum;
    {
        let mut fse = FSE::new(5);

        let mut input: Vec<u32> = vec![10, 10, 12];
        normalize_to_total_sum(&mut input, fse.get_table_size() as u32);
        let stt: SymbolTransformTable =
            fse.generate_symbol_transformation_table(&input);
        let state_table: EncIdxToSymbol = fse.generate_state_table(&input);
        let mut range_list: RangeList = fse.generate_range_list(&input);

        println!("Sym Transform Table {:?}", stt);

        println!("state_table {:?}", state_table);

        println!("state list {:?}", range_list);

        let ct: CodingTable =
            fse.generate_coding_table(&mut range_list, &state_table);
        let dec_table: DecodingTable =
            fse.generate_decoding_table(&input, &state_table);

        println!("Decode table:");
        for dec in dec_table.iter() {
            println!("Decode table {:?}", dec);
        }

        println!("coding table {:?}", ct);

        let data: Vec<u8> = vec![1, 1, 0, 2, 0, 1, 0, 1, 2, 0];
        let _state = fse.encode_data(&data, &ct, &stt);

        let res = fse.decode_data(&dec_table);
        assert_eq!(data, res);
    }
}

impl FSE {
    pub fn round_trip(&mut self, data: &[u8]) {
        let mut hist = Histogram::<256>::from_data(data);
        hist.normalize(self.get_table_size());
        let norm_hist = hist.get_bins();

        let stt: SymbolTransformTable =
            self.generate_symbol_transformation_table(norm_hist);
        let enc_idx_to_sym: EncIdxToSymbol =
            self.generate_state_table(norm_hist);
        let mut occurences: RangeList = self.generate_range_list(norm_hist);

        let ct: CodingTable =
            self.generate_coding_table(&mut occurences, &enc_idx_to_sym);
        let dec_table: DecodingTable =
            self.generate_decoding_table(norm_hist, &enc_idx_to_sym);

        let _state = self.encode_data(data, &ct, &stt);

        let res = self.decode_data(&dec_table);
        println!("res = {:?}", res);
        assert_eq!(data, res);
    }
}

#[test]
fn test_round_trip() {
    let input = "hello world".as_bytes();
    let mut fse = FSE::new(10);
    fse.round_trip(input);
}
