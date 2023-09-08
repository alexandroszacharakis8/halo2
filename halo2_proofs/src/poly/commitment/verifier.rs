use group::{
    ff::{BatchInvert, Field},
    Curve,
};
use group::prime::PrimeCurveAffine;
use pasta_curves::EqAffine;
use pasta_curves::vesta::{Affine, Scalar};
use crate::{wrapper_ec::*, rescue_transcript::RescueRead};

use super::super::Error;
use super::{Params, MSM};
use crate::transcript::{EncodedChallenge, TranscriptRead, Transcript};

use crate::arithmetic::{best_multiexp, CurveAffine};


/// A guard returned by the verifier
#[derive(Debug, Clone)]
pub struct Guard<'a, C: CurveAffine, E: EncodedChallenge<C>> {
    msm: MSM<'a, C>,
    neg_c: C::Scalar,
    u: Vec<C::Scalar>,
    u_packed: Vec<E>,
}

/// An accumulator instance consisting of an evaluation claim and a proof.
#[derive(Debug, Clone)]
pub struct Accumulator<C: CurveAffine, E: EncodedChallenge<C>> {
    /// The claimed output of the linear-time polycommit opening protocol
    pub g: C,

    /// A vector of challenges u_0, ..., u_{k - 1} sampled by the verifier, to
    /// be used in computing G'_0.
    pub u_packed: Vec<E>,
}

impl<'a, C: CurveAffine, E: EncodedChallenge<C>> Guard<'a, C, E> {
    /// Lets caller supply the challenges and obtain an MSM with updated
    /// scalars and points.
    pub fn use_challenges(mut self) -> MSM<'a, C> {
        let s = compute_s(&self.u, self.neg_c);
        self.msm.add_to_g_scalars(&s);

        self.msm
    }

    /// Lets caller supply the purported G point and simply appends
    /// [-c] G to return an updated MSM.
    pub fn use_g(mut self, g: C) -> (MSM<'a, C>, Accumulator<C, E>) {
        self.msm.append_term(self.neg_c, g);

        let accumulator = Accumulator {
            g,
            u_packed: self.u_packed,
        };

        (self.msm, accumulator)
    }

    /// Computes G = ⟨s, params.g⟩
    pub fn compute_g(&self) -> C {
        let s = compute_s(&self.u, C::Scalar::ONE);

        best_multiexp(&s, &self.msm.params.g).to_affine()
    }
}

/// Checks to see if the proof represented within `transcript` is valid, and a
/// point `x` that the polynomial commitment `P` opens purportedly to the value
/// `v`. The provided `msm` should evaluate to the commitment `P` being opened.
pub fn verify_proof<'a, C: CurveAffine, E: EncodedChallenge<C>, T: TranscriptRead<C, E>>(
    params: &'a Params<C>,
    mut msm: MSM<'a, C>,
    transcript: &mut T,
    x: C::Scalar,
    v: C::Scalar,
) -> Result<Guard<'a, C, E>, Error> {
    let k = params.k as usize;
    let p = msm.clone().eval_only().to_affine();
    println!("Valid init msm: {:?}", p);

    // P' = P - [v] G_0 + [ξ] S
    msm.add_constant_term(-v); // add [-v] G_0

    let p = msm.clone().eval_only().to_affine();
    println!("Valid min v: {:?}", p);
    let s_poly_commitment = transcript.read_point().map_err(|_| Error::OpeningError)?;
    let xi = *transcript.squeeze_challenge_scalar::<()>();
    msm.append_term(xi, s_poly_commitment);

    println!("Valid P prime: {:?}", msm.clone().eval_only().to_affine());

    let z = *transcript.squeeze_challenge_scalar::<()>();

    let mut rounds = vec![];
    for _ in 0..k {
        // Read L and R from the proof and write them to the transcript
        let l = transcript.read_point().map_err(|_| Error::OpeningError)?;
        let r = transcript.read_point().map_err(|_| Error::OpeningError)?;

        let u_j_packed = transcript.squeeze_challenge();
        let u_j = *u_j_packed.as_challenge_scalar::<()>();

        rounds.push((l, r, u_j, /* to be inverted */ u_j, u_j_packed));
    }

    rounds
        .iter_mut()
        .map(|&mut (_, _, _, ref mut u_j, _)| u_j)
        .batch_invert();

    // This is the left-hand side of the verifier equation.
    // P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    let mut u = Vec::with_capacity(k);
    let mut u_packed: Vec<E> = Vec::with_capacity(k);
    for (l, r, u_j, u_j_inv, u_j_packed) in rounds {
        msm.append_term(u_j_inv, l);
        msm.append_term(u_j, r);

        u.push(u_j);
        u_packed.push(u_j_packed);
    }

    // Our goal is to check that the left hand side of the verifier
    // equation
    //     P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    // equals (given b = \mathbf{b}_0, and the prover's values c, f),
    // the right-hand side
    //   = [c] (G'_0 + [b * z] U) + [f] W
    // Subtracting the right-hand side from both sides we get
    //   P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    //   + [-c] G'_0 + [-cbz] U + [-f] W
    //   = 0
    //
    // Note that the guard returned from this function does not include
    // the [-c]G'_0 term.

    let c = transcript.read_scalar().map_err(|_| Error::SamplingError)?;
    let neg_c = -c;
    let f = transcript.read_scalar().map_err(|_| Error::SamplingError)?;
    let b = compute_b(x, &u);
    println!("correct b: {:?}", b);

    msm.add_to_u_scalar(neg_c * &b * &z);
    msm.add_to_w_scalar(-f);

    let guard = Guard {
        msm,
        neg_c,
        u,
        u_packed,
    };

    Ok(guard)
}

/// Checks to see if the proof represented within `transcript` is valid, and a
/// point `x` that the polynomial commitment `P` opens purportedly to the value
/// `v`. The provided `msm` should evaluate to the commitment `P` being opened.
pub fn verify_proof_minimal<'a>(
    params: &'a Params<Affine>,
    p: EqAffine,
    transcript: &mut RescueRead<&[u8]>,
    x: Scalar,
    v: Scalar,
) -> Result<(), Error> {
    let k = params.k as usize;

    // P' = P - [v] G_0 + [ξ] S
    let g_zero = params.g[0];
    let vg0 = mul(&v, &g_zero);
    let p_minus_vg0 = sub(&p, &vg0);

    let s_poly_commitment = transcript.read_point().map_err(|_| Error::OpeningError)?;
    let xi = *transcript.squeeze_challenge_scalar::<()>();
    let xis = mul(&xi, &s_poly_commitment);
    let p_prime = add(&p_minus_vg0, &xis);

    let z = *transcript.squeeze_challenge_scalar::<()>();

    // Vector to store the commitments and challenges of each round, (l, r, u, u). We store twice the
    // u challenges in order to compute each inverse in-place in a next step.
    let mut rounds = vec![];

    // Vector to store the folding vectors of the bases used in Pedersen commitment. We do this during
    // our first loop for simplicity. Note that when doing batch verification this is the O(n) step,
    // and should be batched at the end of the verifier.
    let mut folded_gs = vec![vec![]; k + 1];

    // We initialise it with the base generators
    folded_gs[0] = params.g.clone();
    for round in 0..k {
        // Read L and R from the proof and write them to the transcript
        let l = transcript.read_point().map_err(|_| Error::OpeningError)?;
        let r = transcript.read_point().map_err(|_| Error::OpeningError)?;

        let u_j = transcript.squeeze_challenge();

        // Half at vector at n / 2^(1 + round)
        let half = ((1 << k) / (1 << (round + 1))) as usize;
        let first_half = folded_gs[round][..half].to_vec();
        let mut second_half = folded_gs[round][half..].to_vec();
        second_half.iter_mut().for_each(|a| *a = mul(&u_j, a));

        folded_gs[round + 1] = first_half.iter().zip(second_half.iter()).map(|(r, l)| add(r, l)).collect::<Vec<_>>();

        rounds.push((l, r, u_j, /* to be inverted */ u_j));
    }

    assert_eq!(folded_gs[k].len(), 1);

    rounds.iter_mut().for_each(|(_,_,_,u)| { *u = scalar_inversion(u)});
    
    // P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    // This is the left-hand side of the verifier equation.
    let lhs = rounds.iter_mut().fold(p_prime, |p, (l,r,u,u_inv)| {
        let  l_uinv = mul(u_inv, l);
        let  r_u = mul(u, r);
        let sum = add(&r_u, &l_uinv);
        add(&p, &sum)
    });

    // Our goal is to check that the left hand side of the verifier
    // equation
    //     P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    // equals the right-hand side
    //   = [c] (G'_0 + [b * z] U) + [f] W

    let c = transcript.read_scalar().map_err(|_| Error::SamplingError)?;

    let f = transcript.read_scalar().map_err(|_| Error::SamplingError)?;

    let mut b = Scalar::ONE;
    let mut cur_power = x;

    // Computes $\prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} x^{2^i})$.
    for u_j in rounds.iter().rev().map(|(_, _, u_j, _)| u_j ) {
        b *= Scalar::ONE + &(*u_j * &cur_power);
        cur_power *= cur_power;
    }

    let mut rhs = Affine::identity();
    let u = params.u;
    let w = params.w;

    let scalar_u = scalar_product(&[c, b, z]);

    rhs = add(&rhs, &mul(&scalar_u, &u));
    rhs = add(&rhs, &mul(&f, &w));

    rhs = add(&rhs, &mul(&c, &folded_gs[k][0]));

    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::OpeningError)
    }
}

/// Computes $\prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} x^{2^i})$.
fn compute_b<F: Field>(x: F, u: &[F]) -> F {
    let mut tmp = F::ONE;
    let mut cur = x;
    for u_j in u.iter().rev() {
        tmp *= F::ONE + &(*u_j * &cur);
        cur *= cur;
    }
    tmp
}

/// Computes the coefficients of $g(X) = \prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} X^{2^i})$.
fn compute_s<F: Field>(u: &[F], init: F) -> Vec<F> {
    assert!(!u.is_empty());
    let mut v = vec![F::ZERO; 1 << u.len()];
    v[0] = init;

    for (len, u_j) in u.iter().rev().enumerate().map(|(i, u_j)| (1 << i, u_j)) {
        let (left, right) = v.split_at_mut(len);
        let right = &mut right[0..len];
        right.copy_from_slice(left);
        for v in right {
            *v *= u_j;
        }
    }

    v
}
