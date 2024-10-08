// General plan:

// - We have layout with vertical and horizontal dimension. Data is organized in a matrix (N x M, N <= 2^n, M <= 2^m), appended by zeroes on both dimensions.
// - Vertical dimension is dormant - the pushforward is happening independently along each row of the matrix (i.e., vertical component of the mapping is identity).
// - Horizontal dimension is mapped by multiple counters (for technical reasons they are of the same dimension).

// In reality, our pushforward's counters are sourced from two things: scalars are decomposed into M digits, each occupying a row of the matrix
// and second source is auxiliary counter of size 2^n, determining position in the bucket
// this two counters are then concatenated (in binary) and split into our real counters that we use for the argument
// we commit to "real" counters, and recover the scalars during the same sumcheck

// so, for some of the counters, denote T_i the table of the bits that come from the scalar

// - Spark pushforward commits to:
// 1. Counters
// 2. Access counts.
// - then, after it gets evaluation point r, it generates challenges to compute R = (sum \gamma_i P_i) + \gamma_n * 1

// -- then, we run the following sumcheck - S(x, r_y) R(x, r_y) \prod_i (c_i^* eq_{r_i}) (x, r_y)
// -- we also independently run (\sum_i (c_i^* T_i) (q, y) B(y)) for a challenge point q

// -- this spits out a bunch of openings of c_i^* eq_{r_i} in the same point, and c_i^* T_i - in other point
// -- we then do a sumcheck to make them open in a single point.

//-- now, we make challenge \lambda and finally commit to
// 3. c_i^* (eq_{r_i} + \lambda T_i)
// -- and run an indexed lookup argument for these.

// Now, lookup argument is done for the following polynomial:

// counter data, formatted in a way to have enough rows (as we are only doing parallelization along the "vertical" dimension)

// c c c c
// c c c c
// c c 0 0
// c c c c
// c c c c
// c c 0 0
// c c c c
// c c c c
// c c 0 0



#[derive(Clone, Copy, Debug)]
pub struct DataConfig {
    pub n_polys: usize,
    pub hor_size: usize,
    pub ver_size: usize, 
    pub n_hor_vars: usize,
    pub n_ver_vars: usize,
    _dummy: (),
}

impl DataConfig {
    pub fn new(n_polys: usize, hor_size: usize, ver_size: usize, n_hor_vars: usize, n_ver_vars: usize) -> Self {
        assert!(1 << n_hor_vars >= hor_size);
        assert!(1 << n_ver_vars >= ver_size);
        Self{ n_polys, hor_size, ver_size, n_hor_vars, n_ver_vars, _dummy: () }
    }
}

#[derive(Clone, Copy, Debug)]
pub struct PushforwardConfig {
    pub n_ctrs: usize, // Number of counters.
    pub logsize: usize, // Magnitude of the counters.
    pub data_config: DataConfig, // Input configuration.
    _dummy: ()
}

impl PushforwardConfig {
    pub fn new(n_ctrs: usize, logsize: usize, data_config: DataConfig) -> Self {
        assert!(logsize <= 32); // Will drop to 16 if necessary, probably not a bottleneck.
        Self { n_ctrs, logsize, data_config, _dummy: () }
    }

}


// use ark_ff::{PrimeField};
// use num_traits::PrimInt;
// use rayon::{iter::{IndexedParallelIterator, ParallelIterator}, slice::{ParallelSlice, ParallelSliceMut}};

// // *  *  *  *  *  c1 c1 c1
// // *  *  *  *  *  c1 c1 c1
// // *  *  *  *  *  c1 c1 c1
// // c2 c2 c2 c2 c2 c2 c2 c2
// pub struct DenseMatrix<T> {
//     pub row_size: usize,
//     pub col_size: usize,
//     pub values: Vec<T>,

//     pub row_logsize: usize,
//     pub col_logsize: usize,
// }

// impl<T> DenseMatrix<T> {
//     pub fn new(values: Vec<T>, row_size: usize, col_size: usize, row_logsize: usize, col_logsize: usize) -> Self {
//         assert!(values.len() == row_size * col_size);
//         assert!(1 << row_logsize >= row_size);
//         assert!(1 << col_logsize >= col_size);
//         Self { row_size, col_size, values, row_logsize, col_logsize }
//     }
// }

// pub struct CounterMatrix<NUMERIC: PrimInt> {
//     pub matrix: DenseMatrix<NUMERIC>,
//     pub image_dim: usize, // actual bitsize of this counter
// }


// pub struct PushforwardData<F: PrimeField, const N_POLYS: usize> {
//     pub rows: Vec<Vec<F>>, // each row is actually N_POLYS-packed, i.e. it should be thought of as Vec<Vec<[F; N_POLYS]>>

//     // collision_tracker: this is a polynomial which has 1 for an occupied slot and 0 otherwise, however due 

//     pub row_filling_const: [F; N_POLYS],

//     pub row_logsize: usize, // virtual logsizes of the matrix
//     pub col_logsize: usize,
// }

// pub fn pack_indices<const N_CTRS: usize>(indices: [u16; N_CTRS], logsizes: &[usize; N_CTRS]) -> usize {
//     let mut ret = indices[N_CTRS - 1] as usize;
//     for i in 1..N_CTRS {
//         let j = N_CTRS - i - 1;
//         ret <<= logsizes[j];
//         ret += indices[j] as usize;
//     }
//     ret
// }

// pub fn unpack_indices<const N_CTRS: usize>(mut index: usize, logsizes: &[usize; N_CTRS]) -> [u16; N_CTRS] {
//     let mut ret = [0; N_CTRS];
//     for i in 0..N_CTRS {
//         let tmp = index >> logsizes[i];
//         ret[i] = (index - (tmp << logsizes[i])) as u16;
//         index = tmp;
//     }
//     ret
// }

// /// Low level function to compute the pushforward in the form expected by our protocol
// /// It takes N_POLYS polynomials, and computes the image of each row of each polynomial
// /// using the array of counters.
// /// Row counters should have collective dimension equal to row logsize - so each row of the result will have
// /// the (virtual) size equal to original virtual size.
// /// Column counter has some logsize c, coming from Pippinger algorithm - which means that if original
// /// matrix had col_size s, new matrix will have col_size s << c.
// /// Row counter is computed by the prover directly in this function, and are outputted for user convenience.
// pub fn pushforward_wtns<F: PrimeField, const N_POLYS: usize, const N_CTRS: usize>(
//     polys: &[DenseMatrix<F>; N_POLYS],
//     col_counter: &CounterMatrix<u32>,

//     row_filling_const: [F; N_POLYS], // The thing that will be written into unoccupied bucket elements
//                                      // In our case, it is [0; 1; 1], neutral element of the group
//                                      // Unoccupied *rows* are always zeroized.
// ) -> (PushforwardData<F, N_POLYS>, CounterMatrix<usize>)
// {

//     let DenseMatrix{row_logsize, col_logsize, row_size, col_size, values} = &polys[0];
    
//     let row_size = *row_size;
//     let col_size = *col_size;
//     let row_logsize = *row_logsize;
//     let col_logsize = * col_logsize;

//     for i in 1..N_POLYS {
//         assert!(row_logsize == polys[i].row_logsize);
//         assert!(col_logsize == polys[i].col_logsize);
//         assert!(row_size == polys[i].row_size);
//         assert!(col_size == polys[i].col_size);
//     }

//     assert!(row_logsize == col_counter.matrix.row_logsize);
//     assert!(col_logsize == col_counter.matrix.col_logsize);
//     assert!(row_size == col_counter.matrix.row_size);
//     assert!(col_size == col_counter.matrix.col_size);

//     let c = col_counter.image_dim;

//     let mut bucket_lens = vec![0; col_size << c];
    
//     let mut row_counter = vec![0; row_size * col_size]; // Make maybeuninit later?

//     col_counter.matrix.values.par_chunks(row_size)
//         .zip(row_counter.par_chunks_mut(row_size))
//         .zip(bucket_lens.par_chunks_mut(1 << c))
//         .map(|((col_ctr_chunk, row_ctr_chunk), bucket_chunk)|
//     {
//         for i in 0..row_size {
//             let ctr = col_ctr_chunk[i] as usize;
//             row_ctr_chunk[i] = bucket_chunk[ctr];
//             bucket_chunk[ctr] += 1;
//         }
//     }).count();

//     let mut image : Vec<Vec<F>> = vec![];
//     for i in 0 .. (col_size << c) {
//         image.push(Vec::with_capacity(bucket_lens[i]));
//     }

//     image.par_chunks_mut(1 << c)
//         .enumerate()
//         .map(|(row_id, im_chunk)|
//     {
//         for j in 0..row_size {
//             let global_idx = j + row_id * row_size; 
//             for s in 0..N_POLYS {
//                 im_chunk[col_counter.matrix.values[global_idx] as usize].push(polys[s].values[global_idx])
//             }
//         }
//     }).count();

//     let image_data = PushforwardData {
//         rows: image,
//         row_filling_const,
//         row_logsize,
//         col_logsize: col_logsize << c,
//     };

//     let row_counter = CounterMatrix {
//         matrix: DenseMatrix { row_size, col_size, values: row_counter, row_logsize, col_logsize },
//         image_dim: row_logsize,
//     };

//     (image_data, row_counter)
    
// }

// #[cfg(test)]
// mod tests {
//     use super::*;

//     #[test]
//     fn pack_unpack_ctrs() {
//         let logsizes = [2, 3, 5, 3];
//         for i in 0..(1 << (logsizes.iter().sum::<usize>())) {
//             let expected = pack_indices(unpack_indices(i, &logsizes), &logsizes);
//             assert_eq!(expected, i);
//         }
//     }
// }