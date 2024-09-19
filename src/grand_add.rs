use ark_ff::Field;
#[allow(unused_imports)]
use ark_std::iterable::Iterable;
#[allow(unused_imports)]
use rayon::prelude::*;

use crate::utils::TwistedEdwardsConfig;

pub fn affine_twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [x1, y1, x2, y2] = pts.first_chunk().unwrap();
    vec![*x1 * y2, *x2 * y1, *y1 * y2 - (*x1 * x2).mul_by_a()]
}

pub fn affine_twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 3);
    let [x1y2, x2y1, y1y2_ax1x2] = pts.first_chunk().unwrap();
    vec![(*x1y2 + x2y1), *y1y2_ax1x2, *x1y2 * x2y1]
}

pub fn affine_twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 3);
    let [x, y, xy] = pts.first_chunk().unwrap();
    let d_xy = xy.mul_by_d();
    let z2_d_xy = F::one() - d_xy;
    let z2_p_d_xy = F::one() + d_xy;
    vec![z2_d_xy * x, z2_p_d_xy * y, z2_d_xy * z2_p_d_xy]
}

pub fn affine_twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F> {
    assert_eq!(pts.len(), 4);
    affine_twisted_edwards_add_l3(&affine_twisted_edwards_add_l2(&affine_twisted_edwards_add_l1(pts)))
}


pub fn twisted_edwards_add_l1<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 6);
    let [x1, y1, z1, x2, y2, z2] = pts.first_chunk().unwrap();
    vec![
        *x1 * y2,
        *x2 * y1,
        *y1 * y2 - (*x1 * x2).mul_by_a(),
        *z1 * z2,
    ]
}

pub fn twisted_edwards_add_l2<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [x1y2, x2y1, y1y2_ax1x2, z1z2] = pts.first_chunk().unwrap();
    vec![
        (*x1y2 + x2y1) * z1z2,
        *y1y2_ax1x2 * z1z2,
        z1z2.square(),
        *x1y2 * x2y1,
    ]
}

pub fn twisted_edwards_add_l3<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F>  {
    assert_eq!(pts.len(), 4);
    let [x, y, z2, xy] = pts.first_chunk().unwrap();
    let d_xy = xy.mul_by_d();
    let z2_d_xy = *z2 - d_xy;
    let z2_p_d_xy = *z2 + d_xy;
    vec![
        z2_d_xy * x,
        z2_p_d_xy * y,
        z2_d_xy * z2_p_d_xy,
    ]
}

pub fn twisted_edwards_add<F: Field + TwistedEdwardsConfig>(pts: &[F]) -> Vec<F> {
    twisted_edwards_add_l3(&twisted_edwards_add_l2(&twisted_edwards_add_l1(pts)))
}
