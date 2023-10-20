//! Wrapper module for EC operations. We do not implement this generically,
//! and instead rely solely on the pallas curve.
#![allow(missing_docs)]

use ff::Field;
use group::prime::PrimeCurveAffine;
use group::Curve;
use pasta_curves::vesta::{Affine, Scalar};
use std::ops::Mul;

pub fn add(lhs: &Affine, rhs: &Affine) -> Affine {
    (lhs + rhs).to_affine()
}

pub fn sub(lhs: &Affine, rhs: &Affine) -> Affine {
    (lhs - rhs).to_affine()
}

pub fn mul(lhs: &Scalar, rhs: &Affine) -> Affine {
    rhs.mul(lhs).to_affine()
}

pub fn scalar_inversion(scalar: &Scalar) -> Scalar {
    scalar.invert().expect("Zero is non-invertible")
}

pub fn scalar_product(scalars: &[Scalar]) -> Scalar {
    scalars.iter().product()
}

pub fn scalar_pow(scalar: &Scalar, power: u64) -> Scalar {
    scalar.pow_vartime([power])
}

pub fn own_msm(scalars: &[Scalar], points: &[Affine]) -> Affine {
    let mut result = Affine::identity();
    scalars
        .iter()
        .zip(points.iter())
        .for_each(|(scalar, point)| {
            result = (result + point.mul(scalar).to_affine()).to_affine();
        });

    result
}

#[cfg(test)]
mod test {
    use super::*;
    use crate::arithmetic::best_multiexp;
    use rand_core::OsRng;

    // Just sanity check for the msm
    #[test]
    fn msm() {
        let scalars = (0..10).map(|_| Scalar::random(OsRng)).collect::<Vec<_>>();
        let points = (0..10)
            .map(|_| {
                let a = Scalar::random(OsRng);
                (Affine::generator().mul(&a)).to_affine()
            })
            .collect::<Vec<Affine>>();

        let msm_result = best_multiexp(&scalars, &points).to_affine();

        let own_result = own_msm(&scalars, &points);

        assert_eq!(msm_result, own_result);
    }
}
