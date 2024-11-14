use std::fmt::{Display, Formatter};
use ark_ff::PrimeField;
use crate::{
    cleanup::{
        protocols::{
            gkrs::gkr::GKRLayer,
            splits::SplitAt,
            sumcheck::{SinglePointClaims},
            sumchecks::vecvec_eq::VecVecDeg2Sumcheck
        },
        proof_transcript::TProofTranscript2,
        protocol2::Protocol2,
    },
    polynomial::vecvec::VecVecPolynomial
};
use crate::cleanup::protocols::sumcheck::{BareSumcheckSO, DenseSumcheckObjectSO, GenericSumcheckProtocol};
use crate::cleanup::protocols::sumchecks::dense_eq::DenseDeg2Sumcheck;
use crate::cleanup::utils::algfn::{AlgFn, AlgFnSO};
macro_rules! build_advice_into {
    ($name:ident <$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($held:ty)) => {
        impl <$($l, )*$($x : $xt),+> Into<$held> for $name <$($l, )*$($x),+> {
            fn into(self) -> $held {
                match self {
                    $name::$value(ret) => {ret}
                    _ => {unreachable!()}
                }
            }
        }
        
        impl <'__build_advice_into_macro_lifetime_1, $($l, )*$($x : $xt),+> Into<&'__build_advice_into_macro_lifetime_1 $held> for &'__build_advice_into_macro_lifetime_1 $name <$($l, )*$($x),+> {
            fn into(self) -> &'__build_advice_into_macro_lifetime_1 $held {
                match self {
                    $name::$value(ret) => {ret}
                    _ => {unreachable!()}
                }
            }
        }
    };
}


macro_rules! build_all_advice_intos {

    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($held:ty)) => {
        build_advice_into!($name <$($l, )*$($x : $xt),+>, $value($held));
    };

    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($held:ty), $($other:ident($other_held:ty)),+) => {
        build_advice_into!($name <$($l, )*$($x : $xt),+>, $value($held));
        build_all_advice_intos!($name <$($l, )*$($x : $xt),+>, $($other($other_held)),*);
    };
}

macro_rules! common_advice {
    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>{$($value:ident($held:ty)),*}) => {
        #[derive(Debug)]
        pub enum $name <$($l, )*$($x : $xt),+> {
            $($value($held)),*
        }

        build_all_advice_intos!($name <$($l, )*$($x : $xt),+>, $($value($held)),*);
    };
}

common_advice!(
    SplitVecVecMapGKRAdvice<F: PrimeField>{
        VecVecMAP(Vec<VecVecPolynomial<F>>),
        DenseMAP(Vec<Vec<F>>),
        SPLIT(())
    }
);

impl <F: PrimeField> Display for SplitVecVecMapGKRAdvice<F> {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        match self {
            SplitVecVecMapGKRAdvice::VecVecMAP(_) => {write!(f, "VecVecMAP")}
            SplitVecVecMapGKRAdvice::DenseMAP(_) => {write!(f, "DenseMAP")}
            SplitVecVecMapGKRAdvice::SPLIT(_) => {write!(f, "SPLIT")}
        }
    }
}

impl <F: PrimeField> SplitVecVecMapGKRAdvice<F> {
    fn describe(&self) -> String {
        match self {
            SplitVecVecMapGKRAdvice::VecVecMAP(vv) => {format!("VecVec(N: {} data: {})", vv.len(), vv[0].data.len())}
            SplitVecVecMapGKRAdvice::DenseMAP(d) => {format!("Dense(N: {} data: {})", d.len(), d[0].len())}
            SplitVecVecMapGKRAdvice::SPLIT(_) => { "Split()".to_string() }
        }
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>> for VecVecDeg2Sumcheck<F, Fun> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: SplitVecVecMapGKRAdvice<F>) -> SinglePointClaims<F> {
        #[cfg(debug_assertions)]
        println!(
            "Proving layer {} with claim point len {}, claim evs len {}, and advice {}",
            <VecVecDeg2Sumcheck<F, Fun> as GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>::description(self),
            claims.point.len(),
            claims.evs.len(),
            advice.describe()
        );
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }

    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("VecVec: {} nvars {}x{} {}->{}, deg: {}", self.f.description(), self.num_vertical_vars, self.num_vars - self.num_vertical_vars, self.f.n_ins(), self.f.n_outs(), self.f.deg()).to_string()
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>> for DenseDeg2Sumcheck<F, Fun> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: SplitVecVecMapGKRAdvice<F>) -> SinglePointClaims<F> {
        #[cfg(debug_assertions)]
        println!(
            "Proving layer {} with claim point len {}, claim evs len {}, and advice {}",
            <DenseDeg2Sumcheck<F, Fun> as GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>::description(self),
            claims.point.len(),
            claims.evs.len(),
            advice.describe()
        );
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
    
    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("Dense: {} nvars {} {}->{}, deg: {}", self.f.description(), self.num_vars, self.f.n_ins(), self.f.n_outs(), self.f.deg()).to_string()
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField> GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>> for SplitAt<F> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: SplitVecVecMapGKRAdvice<F>) -> SinglePointClaims<F> {
        #[cfg(debug_assertions)]
        println!(
            "Proving layer {} with claim point len {}, claim evs len {}, and advice {}",
            <SplitAt<F> as GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>>>::description(self),
            claims.point.len(),
            claims.evs.len(),
            advice.describe()
        );
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }

    #[cfg(debug_assertions)]
    fn description(&self) -> String {
        format!("Split: at {:?}, by {}", self.var_idx, self.bundle_size).to_string()
    }
}
