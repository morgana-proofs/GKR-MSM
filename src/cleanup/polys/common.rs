use ark_ff::PrimeField;
use ark_ec::twisted_edwards::TECurveConfig;
use rand::Rng;
use crate::cleanup::protocols::splits::SplitIdx;
use crate::cleanup::utils::algfn::AlgFn;

pub trait EvaluateAtPoint<F: PrimeField> {
    fn evaluate(&self, p: &[F]) -> F;
}

pub trait BindVar<F: PrimeField> {
    fn bind(self, t: F) -> Self;
}

pub trait BindVar21<F: PrimeField> {
    fn bind_21(&mut self, t: F);
}

pub trait Make21<F: PrimeField> {
    fn make_21(&mut self);
}

pub trait MapSplit<F: PrimeField>: Sized {
    fn algfn_map_split<Fnc: AlgFn<F>>(
        polys: &[Self],
        func: Fnc,
        var_idx: SplitIdx,
        bundle_size: usize,
    ) -> Vec<Self>;

    fn algfn_map<Fnc: AlgFn<F>>(
        polys: &[Self],
        func: Fnc
    ) -> Vec<Self>;
}

pub trait RandomlyGeneratedPoly<F: PrimeField>: Sized {
    type Config;
    fn rand_points<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, cfg: Self::Config) -> [Self; 3];

    fn rand_points_affine<
        CC: TECurveConfig<BaseField=F>,
        RNG: Rng,
    >(rng: &mut RNG, cfg: Self::Config) -> [Self; 2];

}

pub trait Densify<F: Clone> {
    type Hint;
    fn to_dense(&self, hint: Self::Hint) -> Vec<F>;
}
