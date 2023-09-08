use std::collections::BTreeMap;
use std::ops::Mul;
use ff::Field;
use group::Curve;
use group::prime::PrimeCurveAffine;
use pasta_curves::EqAffine;
use pasta_curves::vesta::{Affine, Scalar};

use super::super::{
    commitment::{Guard, Params, MSM},
    Error,
};
use super::{
    construct_intermediate_sets, ChallengeX1, ChallengeX2, ChallengeX3, ChallengeX4,
    CommitmentReference, Query, VerifierQuery,
};
use crate::arithmetic::{eval_polynomial, lagrange_interpolate, CurveAffine};
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
pub fn verify_proof_minimal<
    'r,
    'params: 'r,
    I,
>(
    params: &'params Params<Affine>,
    transcript: &mut RescueRead<&[u8]>,
    queries: I,
) -> Result<(), Error>
    where
        I: IntoIterator<Item = VerifierQuery<'r, 'params, Affine>> + Clone,
{
    use crate::transcript::Transcript;
    // Sample x_1 for compressing openings at the same point sets together
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();

    // Sample a challenge x_2 for keeping the multi-point quotient
    // polynomial terms linearly independent.
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    let (commitment_map, point_sets) = construct_intermediate_sets(queries);

    // Compress the commitments and expected evaluations at x together.
    // using the challenge x_1
    let mut q_commitments: Vec<_> = vec![
        (EqAffine::identity(), Scalar::ONE); // (accumulator, next x_1 power).
        point_sets.len()];

    // A vec of vecs of evals. The outer vec corresponds to the point set,
    // while the inner vec corresponds to the points in a particular set.
    let mut q_eval_sets = Vec::with_capacity(point_sets.len());
    for point_set in point_sets.iter() {
        q_eval_sets.push(vec![Scalar::ZERO; point_set.len()]);
    }

    {
        let mut accumulate = |set_idx: usize, new_commitment: CommitmentReference<'_, '_, Affine>, evals: Vec<Scalar>| {
            let (q_commitment, x_1_power) = &mut q_commitments[set_idx];
            match new_commitment {
                CommitmentReference::Commitment(c) => {
                    // println!("Commitment (verifier): {:?}", c);
                    *q_commitment = (*q_commitment + (c.mul(*x_1_power))).to_affine();
                }
                CommitmentReference::MSM(msm) => {
                    // println!("Commitment (verifier): {:?}", msm.clone().eval_only().to_affine());
                    let appended_term = msm.clone().eval_only().mul(*x_1_power).to_affine();
                    *q_commitment = (*q_commitment + appended_term).to_affine();
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
            Scalar::ZERO,
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

    // Compute P (the final commitment that has to be opened)
    let mut p = q_prime_commitment;
    let mut v = msm_eval.clone();
    q_commitments.into_iter().zip(u.iter()).for_each(|((q_commitment, _), q_eval)| {
        p = p.mul(*x_4).to_affine();
            p = (p + q_commitment).to_affine();
        v = v * *x_4;
        v = v + q_eval;
    });

    // Verify the opening proof
    super::commitment::verify_proof_minimal(params, p, transcript, *x_3, v)
}

/// Verify a multi-opening proof
pub fn verify_proof_minimal_no_sets<
    'r,
    'params: 'r,
    I,
>(
    params: &'params Params<Affine>,
    transcript: &mut RescueRead<&[u8]>,
    queries: I,
) -> Result<(), Error>
    where
        I: IntoIterator<Item = VerifierQuery<'r, 'params, Affine>> + Clone,
{
    use crate::transcript::Transcript;
    // Sample x_1 for compressing openings at the same point sets together
    let x_1: ChallengeX1<_> = transcript.squeeze_challenge_scalar();

    // Sample a challenge x_2 for keeping the multi-point quotient
    // polynomial terms linearly independent.
    let x_2: ChallengeX2<_> = transcript.squeeze_challenge_scalar();

    // let (commitment_map, point_sets) = construct_intermediate_sets(queries);

    // We omit the optimisation of the multi point opening. Each opening point will have one aggregate polynomial,
    // meaning that we will include some polynomials in more than one aggregate polynomial (see 4.1.5)

    // First we create a mapping from point to it's index. This defines the ordering of the aggregate
    // polynomials.
    let mut point_index_map = BTreeMap::new();

    for query in queries.clone() {
        let num_points = point_index_map.len();
        point_index_map.entry(query.get_point()).or_insert(num_points);
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
        match query.commitment {
            CommitmentReference::Commitment(c) => {
                *q_commitment = (q_commitment.mul(*x_1) + c).to_affine();
            }
            CommitmentReference::MSM(msm) => {
                let appended_term = msm.clone().eval_only().to_affine();
                *q_commitment = (q_commitment.mul(*x_1) + appended_term).to_affine();
            }
        }

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
    let msm_eval = point_index_map.into_iter()
        .fold(
            Scalar::ZERO,
            |msm_eval, (point, index)| {
                let r_poly = lagrange_interpolate(&[point], &[evals[index]]);
                let r_eval = eval_polynomial(&r_poly, *x_3);
                let eval = (u[index] - &r_eval) * &(*x_3 - point).invert().unwrap();
                msm_eval * &(*x_2) + &eval
            },
        );

    // Sample a challenge x_4 that we will use to collapse the openings of
    // the various remaining polynomials at x_3 together.
    let x_4: ChallengeX4<_> = transcript.squeeze_challenge_scalar();

    // Compute P (the final commitment that has to be opened)
    let mut p = q_prime_commitment;
    let mut v = msm_eval.clone();
    q_commitments.into_iter().zip(u.iter()).for_each(|(q_commitment, q_eval)| {
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

// // Compute the Qi's
// fn construct_intermediate_sets<F: Field + Ord, I, Q: Query<F>>(queries: I) -> IntermediateSets<F, Q>
//     where
//         I: IntoIterator<Item = Q> + Clone,
// {
//     // Construct sets of unique commitments and corresponding information about
//     // their queries.
//     let mut commitment_map: Vec<CommitmentData<Q::Eval, Q::Commitment>> = vec![];
//
//     // Also construct mapping from a unique point to a point_index. This defines
//     // an ordering on the points.
//     let mut point_index_map = BTreeMap::new();
//
//     // Iterate over all of the queries, computing the ordering of the points
//     // while also creating new commitment data.
//     for query in queries.clone() {
//         let num_points = point_index_map.len();
//         let point_idx = point_index_map
//             .entry(query.get_point())
//             .or_insert(num_points);
//
//         if let Some(pos) = commitment_map
//             .iter()
//             .position(|comm| comm.commitment == query.get_commitment())
//         {
//             commitment_map[pos].point_indices.push(*point_idx);
//         } else {
//             let mut tmp = CommitmentData::new(query.get_commitment());
//             tmp.point_indices.push(*point_idx);
//             commitment_map.push(tmp);
//         }
//     }
//
//     // Also construct inverse mapping from point_index to the point
//     let mut inverse_point_index_map = BTreeMap::new();
//     for (&point, &point_index) in point_index_map.iter() {
//         inverse_point_index_map.insert(point_index, point);
//     }
//
//     // Construct map of unique ordered point_idx_sets to their set_idx
//     let mut point_idx_sets = BTreeMap::new();
//     // Also construct mapping from commitment to point_idx_set
//     let mut commitment_set_map = Vec::new();
//
//     for commitment_data in commitment_map.iter() {
//         let mut point_index_set = BTreeSet::new();
//         // Note that point_index_set is ordered, unlike point_indices
//         for &point_index in commitment_data.point_indices.iter() {
//             point_index_set.insert(point_index);
//         }
//
//         // Push point_index_set to CommitmentData for the relevant commitment
//         commitment_set_map.push((commitment_data.commitment, point_index_set.clone()));
//
//         let num_sets = point_idx_sets.len();
//         point_idx_sets.entry(point_index_set).or_insert(num_sets);
//     }
//
//     // Initialise empty evals vec for each unique commitment
//     for commitment_data in commitment_map.iter_mut() {
//         let len = commitment_data.point_indices.len();
//         commitment_data.evals = vec![Q::Eval::default(); len];
//     }
//
//     // Populate set_index, evals and points for each commitment using point_idx_sets
//     for query in queries {
//         // The index of the point at which the commitment is queried
//         let point_index = point_index_map.get(&query.get_point()).unwrap();
//
//         // The point_index_set at which the commitment was queried
//         let mut point_index_set = BTreeSet::new();
//         for (commitment, point_idx_set) in commitment_set_map.iter() {
//             if query.get_commitment() == *commitment {
//                 point_index_set = point_idx_set.clone();
//             }
//         }
//         assert!(!point_index_set.is_empty());
//
//         // The set_index of the point_index_set
//         let set_index = point_idx_sets.get(&point_index_set).unwrap();
//         for commitment_data in commitment_map.iter_mut() {
//             if query.get_commitment() == commitment_data.commitment {
//                 commitment_data.set_index = *set_index;
//             }
//         }
//         let point_index_set: Vec<usize> = point_index_set.iter().cloned().collect();
//
//         // The offset of the point_index in the point_index_set
//         let point_index_in_set = point_index_set
//             .iter()
//             .position(|i| i == point_index)
//             .unwrap();
//
//         for commitment_data in commitment_map.iter_mut() {
//             if query.get_commitment() == commitment_data.commitment {
//                 // Insert the eval using the ordering of the point_index_set
//                 commitment_data.evals[point_index_in_set] = query.get_eval();
//             }
//         }
//     }
//
//     // Get actual points in each point set
//     let mut point_sets: Vec<Vec<F>> = vec![Vec::new(); point_idx_sets.len()];
//     for (point_idx_set, &set_idx) in point_idx_sets.iter() {
//         for &point_idx in point_idx_set.iter() {
//             let point = inverse_point_index_map.get(&point_idx).unwrap();
//             point_sets[set_idx].push(*point);
//         }
//     }
//
//     (commitment_map, point_sets)
// }
