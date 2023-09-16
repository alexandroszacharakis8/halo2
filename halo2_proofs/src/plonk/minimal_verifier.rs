use ff::{Field, PrimeField};
use pasta_curves::{EqAffine, Fp};
use std::iter;
use crate::plonk::{Any, Column};

use super::{
    vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    VerifyingKey,
};
use crate::poly::multiopen::MinimalVerifierQuery;
use crate::poly::{
    commitment::{Params, MSM},
    multiopen,
};
use crate::rescue_transcript::RescueRead;
use crate::transcript::{read_n_points, read_n_scalars, Transcript, TranscriptRead};

/// A verifier that checks a single proof at a time.
#[derive(Debug)]
pub struct MinimalSingleVerifier<'params> {
    msm: MSM<'params, EqAffine>,
}

impl<'params> MinimalSingleVerifier<'params> {
    fn process(
        self,
        f: impl FnOnce(MSM<'params, EqAffine>) -> Result<(), Error>,
    ) -> Result<(), Error> {
        f(self.msm)
    }

    /// Constructs a new single proof verifier.
    pub fn new(params: &'params Params<EqAffine>) -> Self {
        MinimalSingleVerifier {
            msm: MSM::new(params),
        }
    }
}

/// Returns a boolean indicating whether or not the proof is valid
pub fn minimal_verify_proof(
    params: &Params<EqAffine>,
    vk: &VerifyingKey<EqAffine>,
    strategy: MinimalSingleVerifier,
    _instances: &[&[&[Fp]]],
    transcript: &mut RescueRead<&[u8]>,
) -> Result<(), Error> {
    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    let advice_commitments =
            // Hash the prover's advice commitments into the transcript
            read_n_points(transcript, vk.cs.num_advice_columns)?;

    println!("Nr advice comm: {:?}", advice_commitments.len());

    // Sample theta challenge for keeping lookup columns linearly independent
    // Even if we don't have lookups, we need to keep this in order to be consistent with the transcript
    let _theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    let permutations_committed =
            // Hash each permutation product commitment
            vk.cs.permutation.read_product_commitments(vk, transcript)?;
    // Nr of permutations should match the following. Unclear why we have three.
    println!(
        "Nr permutations commitments: {:?}",
        permutations_committed.permutation_product_commitments.len()
    );

    let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;

    // Sample y challenge, which keeps the gates linearly independent.
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;
    println!(
        "Number of vanishing polynomials: {:?}",
        vanishing.h_commitments.len()
    );

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let instance_evals = read_n_scalars(transcript, vk.cs.instance_queries.len())?;
    println!("Number of instance evals: {:?}", instance_evals.len());

    let advice_evals = read_n_scalars(transcript, vk.cs.advice_queries.len())?;
    println!("Number of advice evals: {:?}", instance_evals.len());

    let fixed_evals = read_n_scalars(transcript, vk.cs.fixed_queries.len())?;
    println!("Number of fixed evals: {:?}", instance_evals.len());

    let vanishing = vanishing.evaluate_after_x(transcript)?;

    // TODO: Not sure what this is for
    let permutations_common = vk.permutation.evaluate(transcript)?;
    println!(
        "Common evaluations: {:?}",
        permutations_common.permutation_evals.len()
    );

    let permutations_evaluated = permutations_committed.evaluate(transcript)?;
    println!(
        "Permutations evaluated: {:?}",
        permutations_evaluated.sets.len()
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

        // Compute the expected value of h(x)
        let expressions = {
            let fixed_evals = &fixed_evals;
            let advice_evals = &advice_evals;
            let _instance_evals = &instance_evals; // No instance values in our example

            // Just checking the order of our columns
            println!("Columns: {:?}", vk.cs.permutation.columns);
            println!("Number of fixed/advice evals: {:?}/{:?}", fixed_evals.len(), advice_evals.len());

            // We have only one gate, which we evaluate directly. However, it's not completely clear
            // why we have two evaluations of fixed columns. One for the selector (which we use here),
            // but what is `fixed_evals[0]`.
            iter::once(fixed_evals[1] * (advice_evals[0] * advice_evals[1] - advice_evals[2]))
                // Now we work on the permutation argument
                // Enforce only for the first set.
                // l_0(X) * (1 - z_0(X)) = 0
                // We chain the evaluation of that polynomial
                .chain(
                    permutations_evaluated
                        .sets
                        .first()
                        .map(|first_set| l_0 * &(Fp::ONE - &first_set.permutation_product_eval)),
                )
                // Next we enforce only for the last set.
                // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                .chain(permutations_evaluated.sets.last().map(|last_set| {
                    &l_last *
                        & (last_set.permutation_product_eval.square()
                            - &last_set.permutation_product_eval)
                }))
                // Except for the first set, enforce.
                // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                .chain(
                    permutations_evaluated
                        .sets
                        .iter()
                        .skip(1)
                        .zip(permutations_evaluated.sets.iter())
                        .map(|(set, last_set)| {
                            (
                                set.permutation_product_eval,
                                last_set.permutation_product_last_eval.unwrap(),
                            )
                        })
                        .map(move |(set, prev_last)| (set - &prev_last) * &l_0),
                )
                // And for all the sets we enforce:
                // (1 - (l_last(X) + l_blind(X))) * (
                //   z_i(\omega X) \prod (p(X) + \beta s_i(X) + \gamma)
                // - z_i(X) \prod (p(X) + \delta^i \beta X + \gamma)
                // )
                //
                // The order of our columns in the permutation argument is:
                // 1. Fixed column
                // 2. Advice column
                // 3. Advice column
                .chain(
                    permutations_evaluated
                        .sets
                        .iter()
                        .zip(vk.cs.permutation.columns.chunks(1)) // Chunk len = 1, but still have to figure out why
                        .zip(permutations_common.permutation_evals.chunks(1))
                        .enumerate()
                        .map(move |(chunk_index, ((set, columns), permutation_evals))| {
                            let mut left = set.permutation_product_next_eval;
                            // Chunk one, so we only have one column.
                            let col = match columns[0].column_type() {
                                Any::Advice => advice_evals[vk.cs.get_any_query_index(columns[0])],
                                Any::Fixed => fixed_evals[vk.cs.get_any_query_index(columns[0])],
                                _ => panic!("This should not happen in our example")
                            };
                            left *= &(col + &(*beta * permutation_evals[0]) + &*gamma);

                            let mut right = set.permutation_product_eval;
                            let mut current_delta = (*beta * &*x)
                                * &(Fp::DELTA
                                    .pow_vartime([(chunk_index) as u64])); // chunk_len = 1 :shrug:
                            right *= &(col + &current_delta + &*gamma);

                            (left - &right) * (Fp::ONE - &(l_last + &l_blind))
                        }),
                )
        };

        vanishing.verify(params, expressions, y, xn)
    };

    let queries = {
        iter::empty()
            .chain(vk.cs.advice_queries.iter().enumerate().map(
                move |(query_index, &(column, at))| MinimalVerifierQuery {
                    point: vk.domain.rotate_omega(*x, at),
                    commitment: advice_commitments[column.index()],
                    eval: advice_evals[query_index],
                },
            ))
            .chain(permutations_evaluated.queries_minimal(vk, x))
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
    .chain(permutations_common.minimal_queries(&vk.permutation, x))
    .chain(vanishing.minimal_queries(x));

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    strategy.process(|_msm| {
        multiopen::verify_proof_minimal_no_sets(params, transcript, queries)
            .map_err(|_| Error::Opening)
    })
}

// /// Returns a boolean indicating whether or not the proof is valid
// pub fn minimal_verify_proof_fixed(
//     params: &Params<EqAffine>,
//     vk: &VerifyingKey<EqAffine>,
//     strategy: MinimalSingleVerifier,
//     _instances: &[&[&[Fp]]],
//     transcript: &mut RescueRead<&[u8]>,
// ) -> Result<(), Error> {
//     // Hash verification key into transcript
//     vk.hash_into(transcript)?;
//
//     // For our simple example, we have only 2 advice columns
//     let advice_commitments = (0..2).map(|_| transcript.read_point()?).collect::<Vec<_>>();
//
//     // Sample theta challenge for keeping lookup columns linearly independent
//     // Even if we don't have lookups, we need to keep this in order to be consistent with the transcript
//     let _theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();
//
//     // Sample beta challenge
//     let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();
//
//     // Sample gamma challenge
//     let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();
//
//     // Both columns are enabled, but we don't have equality constraints, so we have a single
//     // commitment for the permutation argument (https://zcash.github.io/halo2/design/proving-system/circuit-commitments.html#committing-to-the-equality-constraint-permutation)
//     let permutations_committed = transcript.read_point()?;
//
//     // We now read the vanishing polynomial
//     let vanishing = transcript.read_point()?;
//
//     // Sample y challenge, which keeps the gates linearly independent.
//     let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();
//
//     // Our gate has degree 2, and we have `n` as 2^4, so we have that the polynomial H(X)
//     // has degree 2(2^4 - 1) - 2^4 = 2^4 - 2, meaning that the polynomial can be committed
//     // in a single point, so we shouldn't have any additional commitments here
//     // let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;
//
//     // Sample x challenge, which is used to ensure the circuit is
//     // satisfied with high probability.
//     let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
//
//     // In our example we have no instance columns
//     // let instance_evals = (0..num_proofs)
//     //     .map(|_| -> Result<Vec<_>, _> { read_n_scalars(transcript, vk.cs.instance_queries.len()) })
//     //     .collect::<Result<Vec<_>, _>>()?;
//
//     // We have two advice columns, and we evaluate one of them at x and wx, and the other at x
//     let advice_evals = (0..3).map(|_| transcript.read_scalar()?).collect::<Vec<_>>();
//
//     // No fixed evals
//     // let fixed_evals = read_n_scalars(transcript, vk.cs.fixed_queries.len())?;
//
//
//     let vanishing_eval = transcript.read_scalar()?;
//
//     // We get the number of commitment of the permutation polynomial (one)
//     let permutations_common = (0..2).map(|_| transcript.read_scalar()?).collect::<Vec<_>>();
//     //     let permutations_common = vk.permutation.evaluate(transcript)?;
//
//     // The permutation commitment is evaluated at two points:
//     // * Current
//     // * Next
//     let permutations_evaluated = (permutations_committed, transcript.read_scalar()?, transcript.read_scalar()?);
//     // let permutations_evaluated = permutations_committed
//     //     .into_iter()
//     //     .map(|permutation| permutation.evaluate(transcript))
//     //     .collect::<Result<Vec<_>, _>>()?;
//
//     // This check ensures the circuit is satisfied so long as the polynomial
//     // commitments open to the correct values.
//     let vanishing = {
//         // x^n
//         let xn = x.pow([params.n, 0, 0, 0]);
//
//         let blinding_factors = vk.cs.blinding_factors();
//         let l_evals = vk
//             .domain
//             .l_i_range(*x, xn, (-((blinding_factors + 1) as i32))..=0);
//         assert_eq!(l_evals.len(), 2 + blinding_factors);
//         let l_last = l_evals[0];
//         let l_blind: Fp = l_evals[1..(1 + blinding_factors)]
//             .iter()
//             .fold(Fp::ZERO, |acc, eval| acc + eval);
//         let l_0 = l_evals[1 + blinding_factors];
//
//         // Compute the expected value of h(x)
//         let expressions = advice_evals
//             .iter()
//             .zip(instance_evals.iter())
//             .zip(permutations_evaluated.iter())
//             .flat_map(|((advice_evals, instance_evals), permutation)| {
//                 let fixed_evals = &fixed_evals;
//                 std::iter::empty()
//                     // Evaluate the circuit using the custom gates provided
//                     .chain(vk.cs.gates.iter().flat_map(move |gate| {
//                         gate.polynomials().iter().map(move |poly| {
//                             poly.evaluate(
//                                 &|scalar| scalar,
//                                 &|_| panic!("virtual selectors are removed during optimization"),
//                                 &|query| fixed_evals[query.index],
//                                 &|query| advice_evals[query.index],
//                                 &|query| instance_evals[query.index],
//                                 &|a| -a,
//                                 &|a, b| a + &b,
//                                 &|a, b| a * &b,
//                                 &|a, scalar| a * &scalar,
//                             )
//                         })
//                     }))
//                     .chain(permutation.expressions(
//                         vk,
//                         &vk.cs.permutation,
//                         &permutations_common,
//                         advice_evals,
//                         fixed_evals,
//                         instance_evals,
//                         l_0,
//                         l_last,
//                         l_blind,
//                         beta,
//                         gamma,
//                         x,
//                     ))
//             });
//
//         vanishing.verify(params, expressions, y, xn)
//     };
//
//     let queries = advice_commitments
//         .iter()
//         .zip(advice_evals.iter())
//         .zip(permutations_evaluated.iter())
//         .flat_map(|((advice_commitments, advice_evals), permutation)| {
//             iter::empty()
//                 .chain(vk.cs.advice_queries.iter().enumerate().map(
//                     move |(query_index, &(column, at))| MinimalVerifierQuery {
//                         point: vk.domain.rotate_omega(*x, at),
//                         commitment: advice_commitments[column.index()],
//                         eval: advice_evals[query_index],
//                     },
//                 ))
//                 .chain(permutation.queries_minimal(vk, x))
//         })
//         .chain(
//             vk.cs
//                 .fixed_queries
//                 .iter()
//                 .enumerate()
//                 .map(|(query_index, &(column, at))| {
//                     MinimalVerifierQuery {
//                         point: vk.domain.rotate_omega(*x, at),
//                         commitment: vk.fixed_commitments[column.index()],
//                         eval: fixed_evals[query_index]
//                     }
//                 }),
//         )
//         .chain(permutations_common.minimal_queries(&vk.permutation, x))
//         .chain(vanishing.minimal_queries(x));
//
//     // We are now convinced the circuit is satisfied so long as the
//     // polynomial commitments open to the correct values.
//     strategy.process(|_msm| {
//         multiopen::verify_proof_minimal_no_sets(params, transcript, queries)
//             .map_err(|_| Error::Opening)
//     })
// }
