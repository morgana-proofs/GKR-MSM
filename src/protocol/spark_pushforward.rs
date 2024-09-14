use ark_ff::{PrimeField};

pub struct DenseMatrixPoly<F: PrimeField> {
    row_size: usize,
    col_size: usize,
    values: Vec<F>,

    row_logsize: usize,
    col_logsize: usize,

    const_row_append: F,
    const_append: F,
}

impl<F: PrimeField> DenseMatrixPoly<F> {
    pub fn new(values: Vec<F>, const_row_append: F, const_append: F, row_size: usize, col_size: usize, row_logsize: usize, col_logsize: usize) -> Self {
        assert!(values.len() == row_size * col_size);
        assert!(1 << row_logsize >= row_size);
        assert!(1 << col_logsize >= col_size);
        Self { row_size, col_size, values, const_row_append, const_append, row_logsize, col_logsize }
    }
}