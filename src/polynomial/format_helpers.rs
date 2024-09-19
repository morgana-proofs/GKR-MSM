use ark_ff::PrimeField;

use super::fragmented::{FragmentContent, FragmentedPoly};

pub struct RowFormatPoly<F: PrimeField> {
    poly: FragmentedPoly<F>,
}

impl<F: PrimeField> RowFormatPoly<F> {
}

impl<F: PrimeField> TryFrom<FragmentedPoly<F>> for RowFormatPoly<F> {
    type Error = String;

    fn try_from(value: FragmentedPoly<F>) -> Result<Self, Self::Error> {
        let shape = value.shape.get().unwrap();
        if (shape.fragments.len() > 2 || shape.fragments.len() == 0) {
            panic!()
            // return Err("Wrong polynomial format - too many fragments.".into());
        }
        if shape.fragments.len() == 2 {
            match shape.fragments[1].content {
                FragmentContent::Data => {
                    panic!()
                    // return Err("Incorrect format.".into())
                },
                _ => (),
            }
        }
        match shape.fragments[0].content {
            FragmentContent::Consts => {
                panic!()
                // return Err("Incorrect format.".into())
            },
            _ => (),
        }

        Ok(RowFormatPoly{ poly: value })
    }
}