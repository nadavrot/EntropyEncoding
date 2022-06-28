pub struct Histogram<const BINS: usize> {
    values: [u32; BINS],
}

impl<const BINS: usize> Histogram<BINS> {
    pub fn from_data<Ty: Into<usize> + Copy>(values: &[Ty]) -> Histogram<BINS> {
        let mut hist = [0; BINS];
        for val in values {
            let val: usize = Into::into(*val);
            hist[val] += 1;
        }

        Histogram { values: hist }
    }

    pub fn get_bins(&self) -> &[u32; BINS] {
        &self.values
    }

    pub fn dump(&self) {
        let mut first_non_zero = BINS;
        let mut last_non_zero = 0;
        let mut max = 0;

        // Find the max value and the non-zero ranges.
        for (i, val) in self.values.iter().enumerate() {
            if *val != 0 {
                first_non_zero = first_non_zero.min(i);
                last_non_zero = last_non_zero.max(i);
                max = max.max(*val);
            }
        }

        if max == 0 {
            println!("-- empty --");
        }

        fn print_bar(index: usize, value: usize, len: usize) {
            print!("{}) ", index);
            for _ in 0..len {
                print!("#");
            }
            println!(" - {}", value);
        }

        // Print the values.
        for i in first_non_zero..last_non_zero + 1 {
            let dots = 40 * self.values[i] / max;
            print_bar(i, self.values[i] as usize, dots as usize);
        }
    }
}

#[test]
fn test_small_generic() {
    let data: Vec<u8> = vec![
        0, 0, 0, 0, 0, 0, 0, 0, 0, 0, // 10
        1, 1, 1, 1, 1, 1, 1, 1, 1, 1, // 10
        2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, // 12
    ];
    let hist: Histogram<3> = Histogram::from_data(&data);
    hist.dump();
}

pub fn num_bits(num: u32) -> u32 {
    let mut num = num;
    let mut cnt = 0;
    while num > 0 {
        num >>= 1;
        cnt += 1;
    }
    cnt
}

#[test]
fn test_num_bits() {
    assert_eq!(num_bits(3), 2);
    assert_eq!(num_bits(7), 3);
    assert_eq!(num_bits(10), 4);
    assert_eq!(num_bits(256), 9);
}

#[test]
fn test_hist() {
    use rand::thread_rng;
    use rand_distr::{Distribution, Normal};

    let mut data: Vec<u8> = Vec::new();

    let mut rng = thread_rng();
    let normal = Normal::new(35.0_f32, 10.0_f32).unwrap();
    for _ in 0..10000 {
        let v = normal.sample(&mut rng);
        data.push(v as u8);
    }

    let hist: Histogram<256> = Histogram::from_data(&data);
    hist.dump();
}

/// Normalize the values in \p values and make the sum of \p values equal to
/// \p total. This is only an approximation.
/// Reference: FSE_normalizeCount and FSE_normalizeM2
pub fn normalize_to_total_sum(values: &mut [u32], total: u32) {
    // If the array contains zero then inc
    if values.iter().any(|z| *z == 0) {
        for val in values.iter_mut() {
            *val += 1;
        }
    }

    let sum: u32 = values.iter().sum();
    assert!(sum != 0, "histogram is empty");

    for val in values.iter_mut() {
        *val = ((*val as u64 * total as u64) / sum as u64) as u32;
    }

    let sum = values.iter().sum();
    assert!(
        total >= sum,
        "Expected the sum to be lower because we round down"
    );
    let mut gap = total - sum;

    while gap > 0 {
        for val in values.iter_mut() {
            if *val > 0 {
                *val += 1;
                gap -= 1;
            }
            if gap == 0 {
                break;
            }
        }
    }
    let sum: u32 = values.iter().sum();
    assert!(sum == total);
}

#[test]
fn test_normalize() {
    for i in 1..10 {
        let table_size = 1 << i;
        let mut input: Vec<u32> = vec![10, 10, 24];
        println!("{:?}", input);
        normalize_to_total_sum(&mut input, table_size);
        let sum: u32 = input.iter().sum();
        assert_eq!(sum, table_size);
        println!("{:?}", input);
    }
}

impl<const BINS: usize> Histogram<BINS> {
    pub fn normalize(&mut self, total_sum: usize) {
        normalize_to_total_sum(&mut self.values, total_sum as u32);
    }
}
