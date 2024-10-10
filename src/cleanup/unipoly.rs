// use ark_ff::Field;

// pub struct UniPoly<F: Field> {
//     pub coeffs: Vec<F>
// }

// impl<F: Field> UniPoly<F> {
//     pub fn from_coeffs(coeffs: Vec<F>) -> Self {
//         Self { coeffs }
//     }


//     pub fn compress(&self) -> CompressedUniPoly<F> {
//         let mut ret = self.coeffs.to_vec();
//         ret.remove(1);
//         CompressedUniPoly::new(ret)
//     }
    
//     pub fn ev(&self, x: F) -> F {
//         let l = self.coeffs.len();
//         if l == 0 {return F::zero()}
//         let mut ret = self.coeffs[l-1];
    
//         for i in 0..l-1 {
//             ret *= x;
//             ret += self.coeffs[l-2-i];
//         }
    
//         ret
//     }
    
// }


// pub struct CompressedUniPoly<F: Field> {
//     pub coeffs_wo_lterm: Vec<F>,
// }

// impl<F: Field> CompressedUniPoly<F> {
//     pub fn new(coeffs_wo_lterm: Vec<F>) -> Self {
//         CompressedUniPoly { coeffs_wo_lterm }
//     }

//     pub fn decompress(&self, sum: F) -> UniPoly<F> {
//         let l = self.coeffs_wo_lterm.len();
//         let mut sum_minus_lterm = self.coeffs_wo_lterm[0].double();
//         for i in 1..l {
//             sum_minus_lterm += self.coeffs_wo_lterm[i];
//         }
//         let mut ret = Vec::with_capacity(l+1);
//         ret.push(self.coeffs_wo_lterm[0]);
//         ret.push(sum - sum_minus_lterm);
//         ret.extend_from_slice(&self.coeffs_wo_lterm[1..]);
//         UniPoly::from_coeffs(ret)
//     }        
// }