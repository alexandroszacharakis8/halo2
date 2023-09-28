use ff::{Field, PrimeField};
use pasta_curves::{EqAffine, Fp};
use std::iter;
use group::Curve;
use group::prime::PrimeCurveAffine;

use super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    VerifyingKey,
};
use crate::poly::multiopen::MinimalVerifierQuery;
use crate::poly::{commitment::Params, multiopen, Rotation};
use crate::rescue_transcript::RescueRead;
use crate::transcript::{Transcript, TranscriptRead};

/// Returns a boolean indicating whether or not the proof is valid
pub fn minimal_verify_proof(
    params: &Params<EqAffine>,
    vk: &VerifyingKey<EqAffine>,
    _instances: &[&[&[Fp]]],
    transcript: &mut RescueRead<&[u8]>,
) -> Result<(), Error> {
    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    // We have two advice commitments
    let advice_commitments = (0..2)
        .map(|_| transcript.read_point().unwrap())
        .collect::<Vec<_>>();

    // Sample theta challenge for keeping lookup columns linearly independent
    // Even if we don't have lookups, we need to keep this in order to be consistent with the transcript
    let _theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    // We should have three permutations commitments
    let permutations_committed = (0..3)
        .map(|_| transcript.read_point().expect("aha"))
        .collect::<Vec<_>>();

    // Now we read the commitment of a randomly sampled polynomial (step 3 of protocol)
    let vanishing_rand = transcript.read_point().unwrap();

    // Sample y challenge, which keeps the gates linearly independent.
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    // Now we get the commitments of the split H polynomial, which is split in two parts
    // TODO: Wait, why is this split only in two :thinking-face:
    let vanishing_split = (0..2)
        .map(|_| transcript.read_point().expect("Failed here"))
        .collect::<Vec<_>>();

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();

    // We don't have instance evals
    let _instance_evals = (0..0).map(|_| transcript.read_scalar().unwrap())
        .collect::<Vec<_>>();

    // We have three evaluation of advice columns. 1 for each advice, and one for the next of the first advice
    let advice_evals = (0..3)
        .map(|_| transcript.read_scalar().unwrap())
        .collect::<Vec<_>>();

    // We have two evaluations of fixed evals. One for our fixed value and another one for the selector
    let fixed_evals = (0..2)
        .map(|_| transcript.read_scalar().unwrap())
        .collect::<Vec<_>>();

    // Random point to prove correctness of the random commitment of the vanishing polynomial
    let random_eval = transcript.read_scalar()?;

    // Evaluations of the permutations polynomials. We get three scalars.
    let permutations_common_evals = (0..3)
        .map(|_| transcript.read_scalar().unwrap())
        .collect::<Vec<_>>();

    // Now we need the evaluations used to validate the permutation argument, meaning evaluations at the
    // current and next powers of omega, and for all except the last, to the last power of omega.
    // We build three tuples for each split of the polynomial
    let permutations_evaluated_a = (
        permutations_committed[0],
        transcript.read_scalar().unwrap(),
        transcript.read_scalar().unwrap(),
        transcript.read_scalar().unwrap(),
    );
    let permutations_evaluated_b = (
        permutations_committed[1],
        transcript.read_scalar().unwrap(),
        transcript.read_scalar().unwrap(),
        transcript.read_scalar().unwrap(),
    );
    // We don't need the evaluation of the last power of omega for the last one.
    let permutations_evaluated_c = (
        permutations_committed[2],
        transcript.read_scalar().unwrap(),
        transcript.read_scalar().unwrap(),
    );

    // This check ensures the circuit is satisfied so long as the polynomial
    // commitments open to the correct values.
    let vanishing = {
        // x^n
        let xn = x.pow([params.n, 0, 0, 0]);

        let blinding_factors = vk.cs.blinding_factors();
        let l_evals = vk
            .domain
            .l_i_range(*x, xn, (-((blinding_factors + 1) as i32))..=0);
        assert_eq!(l_evals.len(), 2 + blinding_factors);
        let l_last = l_evals[0];
        let l_blind: Fp = l_evals[1..(1 + blinding_factors)]
            .iter()
            .fold(Fp::ZERO, |acc, eval| acc + eval);
        let l_0 = l_evals[1 + blinding_factors];

        // (1 - (l_last(X) + l_blind(X))) * (
        //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
        // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
        // )
        let last_permutation_constraint = |col, col_eval, perm_eval, left: &mut Fp, delta_power: u64| {
            *left *= &(col + &(*beta * col_eval) + &*gamma);

            let mut right = perm_eval;

            let current_delta =
                *beta * *x * &(Fp::DELTA
                    .pow_vartime([delta_power])); // chunk_len = 1
            right *= &(col + &current_delta + &*gamma);

            (*left - &right) * (Fp::ONE - &(l_last + &l_blind))
        };

        // Compute the expected value of h(x)
        let expressions = {
            let fixed_evals = &fixed_evals;
            let advice_evals = &advice_evals;
            let _instance_evals = &_instance_evals; // No instance values in our example

            // We have only one gate, which we evaluate directly.
            // We have two evaluations of fixed columns, one for the fixed column (which we don't use
            // in the gate) and one for the selector (which we use here),
            iter::once(fixed_evals[1] * (advice_evals[0] * advice_evals[1] - advice_evals[2]))
                // Now we work on the permutation argument
                // Enforce only for the first set.
                // l_0(X) * (1 - z_0(X)) = 0
                // CP1 in notes
                .chain(iter::once(l_0 * &(Fp::ONE - &permutations_evaluated_a.1)))
                // Next we enforce only for the last set.
                // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                // CP2 in notes
                .chain(iter::once(
                    &l_last * &(permutations_evaluated_c.1.square() - &permutations_evaluated_c.1),
                ))
                // Except for the first set, enforce.
                // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                // CP3 and CP4 in notes
                .chain(iter::once((permutations_evaluated_b.1 - permutations_evaluated_a.3) * &l_0))
                .chain(iter::once((permutations_evaluated_c.1 - permutations_evaluated_b.3) * &l_0))
                // And for all the sets we enforce:
                // (1 - (l_last(X) + l_blind(X))) * (
                //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
                // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
                // )
                //
                // The order of our columns in the permutation argument is:
                // 1. Fixed column CP7 in notes
                // 2. Advice column CP5 in notes
                // 3. Advice column CP6 in notes
                .chain(iter::once({
                    let mut left = permutations_evaluated_a.2;
                    last_permutation_constraint(fixed_evals[0], permutations_common_evals[0], permutations_evaluated_a.1, &mut left, 0)
                }))
                .chain(iter::once({
                    let mut left = permutations_evaluated_b.2;
                    last_permutation_constraint(advice_evals[0], permutations_common_evals[1], permutations_evaluated_b.1, &mut left, 1)
                }))
                .chain(iter::once({
                    let mut left = permutations_evaluated_c.2;
                    last_permutation_constraint(advice_evals[1], permutations_common_evals[2], permutations_evaluated_c.1, &mut left, 2)
                }))
        };

        // Now we compute the vanishing polynomial expected evaluation
        let expected_h_eval = expressions.fold(Fp::ZERO, |h_eval, v| h_eval * &*y + &v);
        let expected_h_eval = expected_h_eval * ((xn - Fp::ONE).invert().unwrap());

        // and its commitment
        let h_commitment = vanishing_split
            .iter()
            .rev()
            .fold(EqAffine::identity(), |mut acc, commitment| {
                acc = (acc * xn).to_affine();
                acc = (acc + *commitment).to_affine();
                acc
            });

        (h_commitment, expected_h_eval)
    };


    let blinding_factors = vk.cs.blinding_factors();
    let x_next = vk.domain.rotate_omega(*x, Rotation::next());
    let x_last = vk
        .domain
        .rotate_omega(*x, Rotation(-((blinding_factors + 1) as i32)));

    let queries = {
        iter::empty()
            .chain(vk.cs.advice_queries.iter().enumerate().map(
                move |(query_index, &(column, at))| MinimalVerifierQuery {
                    point: vk.domain.rotate_omega(*x, at),
                    commitment: advice_commitments[column.index()],
                    eval: advice_evals[query_index],
                },
            ))
            // Open permutation product commitments at x and \omega x
            .chain(Some(MinimalVerifierQuery {
                point: *x,
                commitment: permutations_evaluated_a.0,
                eval: permutations_evaluated_a.1,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_next,
                commitment: permutations_evaluated_a.0,
                eval: permutations_evaluated_a.2,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: *x,
                commitment: permutations_evaluated_b.0,
                eval: permutations_evaluated_b.1,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_next,
                commitment: permutations_evaluated_b.0,
                eval: permutations_evaluated_b.2,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: *x,
                commitment: permutations_evaluated_c.0,
                eval: permutations_evaluated_c.1,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_next,
                commitment: permutations_evaluated_c.0,
                eval: permutations_evaluated_c.2,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_last,
                commitment: permutations_evaluated_b.0,
                eval: permutations_evaluated_b.3,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_last,
                commitment: permutations_evaluated_a.0,
                eval: permutations_evaluated_a.3,
            }))
    }
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                .map(|(query_index, &(column, at))| MinimalVerifierQuery {
                    point: vk.domain.rotate_omega(*x, at),
                    commitment: vk.fixed_commitments[column.index()],
                    eval: fixed_evals[query_index],
                }),
        )
        .chain(vk.permutation.commitments
            .iter()
            .zip(permutations_common_evals.iter())
            .map(move |(commitment, &eval)| MinimalVerifierQuery {
                point: *x,
                commitment: *commitment,
                eval,
            }))
        .chain(Some(MinimalVerifierQuery {
            point: *x,
            commitment: vanishing.0.clone(),
            eval: vanishing.1,
        }))
        .chain(Some(MinimalVerifierQuery {
            point: *x,
            commitment: vanishing_rand,
            eval: random_eval,
        }));

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    multiopen::verify_proof_minimal(params, transcript, queries)
        .map_err(|_| Error::Opening)
}
