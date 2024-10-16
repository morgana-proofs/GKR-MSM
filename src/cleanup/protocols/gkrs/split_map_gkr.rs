use ark_ff::PrimeField;
use crate::{
    cleanup::{
        protocols::{
            gkrs::gkr::GKRLayer,
            splits::SplitAt,
            sumcheck::{AlgFn, SinglePointClaims},
            sumchecks::vecvec::VecVecDeg2Sumcheck
        },
        proof_transcript::TProofTranscript2,
        protocol2::Protocol2,
    },
    polynomial::vecvec::VecVecPolynomial
};
use crate::cleanup::protocols::sumcheck::{AlgFnSO, BareSumcheckSO, DenseSumcheckObjectSO, GenericSumcheckProtocol};

macro_rules! build_advice_into {
    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($holded:ty)) => {
        impl <$($l, )*$($x : $xt),+> Into<$holded> for $name <$($l, )*$($x),+> {
            fn into(self) -> $holded {
                match self {
                    $name::$value(ret) => {ret}
                    _ => {unreachable!()}
                }
            }
        }
    };
}


macro_rules! build_all_advice_intos {

    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($holded:ty)) => {
        build_advice_into!($name <$($l, )*$($x : $xt),+>, $value($holded));
    };

    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>, $value:ident($holded:ty), $($other:ident($ohter_holded:ty)),+) => {
        build_advice_into!($name <$($l, )*$($x : $xt),+>, $value($holded));
        build_all_advice_intos!($name <$($l, )*$($x : $xt),+>, $($other($ohter_holded)),*);
    };
}

macro_rules! common_advice {
    ($name:ident<$($l:lifetime, )*$($x:ident : $xt:path),+>{$($value:ident($holded:ty)),*}) => {
        #[derive(Debug)]
        pub enum $name <$($l, )*$($x : $xt),+> {
            $($value($holded)),*
        }

        build_all_advice_intos!($name <$($l, )*$($x : $xt),+>, $($value($holded)),*);
    };
}



common_advice!(
    SplitVecVecMapGKRAdvice<F: PrimeField>{
        VecVecMAP(Vec<VecVecPolynomial<F>>),
        DenseMAP(Vec<Vec<F>>),
        SPLIT(())
    }
);

impl<Transcript: TProofTranscript2, F: PrimeField, Fun: AlgFn<F>> GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>> for VecVecDeg2Sumcheck<F, Fun> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: SplitVecVecMapGKRAdvice<F>) -> SinglePointClaims<F> {
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
}

impl<Transcript: TProofTranscript2, F: PrimeField> GKRLayer<Transcript, SinglePointClaims<F>, SplitVecVecMapGKRAdvice<F>> for SplitAt<F> {
    fn prove_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>, advice: SplitVecVecMapGKRAdvice<F>) -> SinglePointClaims<F> {
        Protocol2::prove(self, transcript, claims.into(), advice.into()).0
    }

    fn verify_layer(&self, transcript: &mut Transcript, claims: SinglePointClaims<F>) -> SinglePointClaims<F> {
        Protocol2::verify(self, transcript, claims.into())
    }
}
