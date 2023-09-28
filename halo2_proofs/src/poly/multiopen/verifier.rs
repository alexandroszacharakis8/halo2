use ff::Field;
use group::prime::PrimeCurveAffine;
use group::Curve;
use pasta_curves::vesta::{Affine, Scalar};
use pasta_curves::EqAffine;
use std::collections::BTreeMap;
use std::ops::Mul;

use super::super::{
    commitment::{Guard, Params, MSM},
    Error,
};
use super::{
    construct_intermediate_sets, ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4,
    CommitmentReference, Query, VerifierQuery,
};
use crate::arithmetic::{eval_polynomial, lagrange_interpolate, CurveAffine};
use crate::poly::multiopen::MinimalVerifierQuery;
use crate::rescue_transcript::RescueRead;
use crate::transcript::{EncodedChallenge, TranscriptRead};

/// Verify a multi-opening proof
pub fn verify_proof<
    'r,
    'params: 'r,
    I,
    C: CurveAffine,
    E: EncodedChallenge<C>,
    T: TranscriptRead<C, E>,
>(
    params: &'params Params<C>,
    transcript: &mut T,
    queries: I,
    mut msm: MSM<'params, C>,
) -> Result<Guard<'params, C, E>, Error>
where
    I: IntoIterator<Item = VerifierQuery<'r, 'params, C>> + Clone,
{
    // Sample x_1 for compressing openings at the same point sets together
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();

    // Sample a challenge x_2 for keeping the multi-point quotient
    // polynomial terms linearly independent.
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    let (commitment_map, point_sets) = construct_intermediate_sets(queries);

    // Compress the commitments and expected evaluations at x together.
    // using the challenge x_1
    let mut q_commitments: Vec<_> = vec![
        (params.empty_msm(), C::Scalar::ONE); // (accumulator, next x_1 power).
        point_sets.len()];

    // A vec of vecs of evals. The outer vec corresponds to the point set,
    // while the inner vec corresponds to the points in a particular set.
    let mut q_eval_sets = Vec::with_capacity(point_sets.len());
    for point_set in point_sets.iter() {
        q_eval_sets.push(vec![C::Scalar::ZERO; point_set.len()]);
    }

    {
        let mut accumulate = |set_idx: usize, new_commitment, evals: Vec<C::Scalar>| {
            let (q_commitment, x_1_power) = &mut q_commitments[set_idx];
            match new_commitment {
                CommitmentReference::Commitment(c) => {
                    q_commitment.append_term(*x_1_power, *c);
                }
                CommitmentReference::MSM(msm) => {
                    let mut msm = msm.clone();
                    msm.scale(*x_1_power);
                    q_commitment.add_msm(&msm);
                }
            }
            for (eval, set_eval) in evals.iter().zip(q_eval_sets[set_idx].iter_mut()) {
                *set_eval += (*eval) * (*x_1_power);
            }
            *x_1_power *= *x_1;
        };

        // Each commitment corresponds to evaluations at a set of points.
        // For each set, we collapse each commitment's evals pointwise.
        // Run in order of increasing x_1 powers.
        for commitment_data in commitment_map.into_iter().rev() {
            accumulate(
                commitment_data.set_index,  // set_idx,
                commitment_data.commitment, // commitment,
                commitment_data.evals,      // evals
            );
        }
    }

    // Obtain the commitment to the multi-point quotient polynomial f(X).
    let q_prime_commitment = transcript.read_point().map_err(|_| Error::SamplingError)?;

    // Sample a challenge x_3 for checking that f(X) was committed to
    // correctly.
    let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();

    // u is a vector containing the evaluations of the Q polynomial
    // commitments at x_3
    let mut u = Vec::with_capacity(q_eval_sets.len());
    for _ in 0..q_eval_sets.len() {
        u.push(transcript.read_scalar().map_err(|_| Error::SamplingError)?);
    }

    // We can compute the expected msm_eval at x_3 using the u provided
    // by the prover and from x_2
    let msm_eval = point_sets
        .iter()
        .zip(q_eval_sets.iter())
        .zip(u.iter())
        .fold(
            C::Scalar::ZERO,
            |msm_eval, ((points, evals), proof_eval)| {
                let r_poly = lagrange_interpolate(points, evals);
                let r_eval = eval_polynomial(&r_poly, *x_3);
                let eval = points.iter().fold(*proof_eval - &r_eval, |eval, point| {
                    eval * &(*x_3 - point).invert().unwrap()
                });
                msm_eval * &(*x_2) + &eval
            },
        );

    // Sample a challenge x_4 that we will use to collapse the openings of
    // the various remaining polynomials at x_3 together.
    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    // Compute the final commitment that has to be opened
    msm.append_term(C::Scalar::ONE, q_prime_commitment);
    let (msm, v) = q_commitments.into_iter().zip(u.iter()).fold(
        (msm, msm_eval),
        |(mut msm, msm_eval), ((q_commitment, _), q_eval)| {
            msm.scale(*x_4);
            msm.add_msm(&q_commitment);
            (msm, msm_eval * &(*x_4) + q_eval)
        },
    );

    // Verify the opening proof
    super::commitment::verify_proof(params, msm, transcript, *x_3, v)
}

/// Verify a multi-opening proof
pub fn verify_proof_minimal<'r, 'params: 'r, I>(
    params: &'params Params<Affine>,
    transcript: &mut RescueRead<&[u8]>,
    queries: I,
) -> Result<(), Error>
where
    I: IntoIterator<Item = MinimalVerifierQuery<Affine>> + Clone,
{
    use crate::transcript::Transcript;
    // Sample x_1 for compressing openings at the same point sets together
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();

    // Sample a challenge x_2 for keeping the multi-point quotient
    // polynomial terms linearly independent.
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    // We omit the optimisation of the multi point opening. Each opening point will have one aggregate polynomial,
    // meaning that we will include some polynomials in more than one aggregate polynomial (see 4.1.5)

    // First we create a mapping from point to it's index. This defines the ordering of the aggregate
    // polynomials.
    let mut point_index_map = BTreeMap::new();

    for query in queries.clone() {
        let num_points = point_index_map.len();
        point_index_map
            .entry(query.get_point())
            .or_insert(num_points);
    }

    // Compress the commitments and expected evaluations at x together.
    // using the challenge x_1
    let mut q_commitments: Vec<_> = vec![
        EqAffine::identity(); // (accumulator, next x_1 power).
        point_index_map.len()];

    let mut evals = vec![Scalar::ZERO; point_index_map.len()];

    // Now for each query we add the polynomial to its q aggregate polynomial (by multiplying always with a
    // different power of x_1), which is determined by it's evaluation point.
    for query in queries.clone() {
        let q_comm_index = point_index_map[&query.get_point()];
        let q_commitment = &mut q_commitments[q_comm_index];
        *q_commitment = (q_commitment.mul(*x_1) + query.get_commitment()).to_affine();

        evals[q_comm_index] *= *x_1;
        evals[q_comm_index] += query.get_eval();
    }

    // Obtain the commitment to the multi-point quotient polynomial f(X).
    let q_prime_commitment = transcript.read_point().map_err(|_| Error::SamplingError)?;

    // Sample a challenge x_3 for checking that f(X) was committed to
    // correctly.
    let x_3: ChallengeX3<_> = transcript.squeeze_challenge_scalar();

    // u is a vector containing the evaluations of the Q polynomial
    // commitments at x_3
    let mut u = Vec::with_capacity(point_index_map.len());
    for _ in 0..point_index_map.len() {
        u.push(transcript.read_scalar().map_err(|_| Error::SamplingError)?);
    }

    // We can compute the expected msm_eval at x_3 using the u provided
    // by the prover and from x_2
    let msm_eval = point_index_map
        .into_iter()
        .fold(Scalar::ZERO, |msm_eval, (point, index)| {
            let r_poly = lagrange_interpolate(&[point], &[evals[index]]);
            let r_eval = eval_polynomial(&r_poly, *x_3);
            let eval = (u[index] - &r_eval) * &(*x_3 - point).invert().unwrap();
            msm_eval * &(*x_2) + &eval
        });

    // Sample a challenge x_4 that we will use to collapse the openings of
    // the various remaining polynomials at x_3 together.
    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    // Compute P (the final commitment that has to be opened)
    let mut p = q_prime_commitment;
    let mut v = msm_eval.clone();
    q_commitments
        .into_iter()
        .zip(u.iter())
        .for_each(|(q_commitment, q_eval)| {
            p = p.mul(*x_4).to_affine();
            p = (p + q_commitment).to_affine();
            v = v * *x_4;
            v = v + q_eval;
        });

    // Verify the opening proof
    super::commitment::verify_proof_minimal(params, p, transcript, *x_3, v)
}

impl<'a, 'b, C: CurveAffine> Query<C::Scalar> for VerifierQuery<'a, 'b, C> {
    type Commitment = CommitmentReference<'a, 'b, C>;
    type Eval = C::Scalar;

    fn get_point(&self) -> C::Scalar {
        self.point
    }
    fn get_eval(&self) -> C::Scalar {
        self.eval
    }
    fn get_commitment(&self) -> Self::Commitment {
        self.commitment
    }
}
