//! Wrapper module for EC operations. We do not implement this generically,
//! and instead rely solely on the pallas curve.

use pasta_curves::vesta::{Affine, Scalar};

pub fn add(lhs: &Affine, rhs: &Affine) -> Affine {
    todo!()
}

pub fn sub(lhs: &Affine, rhs: &Affine) -> Affine {
    todo!()
}

pub fn mul(lhs: &Scalar, rhs: &Affine) -> Affine {
    todo!()
}

pub fn scalar_inversion(scalar: &Scalar) -> Scalar {
    todo!()
}

pub fn scalar_product(scalars: &[Scalar]) -> Scalar {
    todo!()
}

pub fn scalar_pow(scalar: &Scalar) -> Scalar {
    todo!()
}

pub fn msm(scalars: &[Scalar], points: &[Affine]) -> Affine {
    todo!()
}

