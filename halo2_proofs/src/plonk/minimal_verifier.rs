use ff::Field;
use pasta_curves::{EqAffine, Fp};
use std::iter;

use super::{
    vanishing, ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    VerifyingKey,
};
use crate::poly::{
    commitment::{Guard, Params, MSM},
    multiopen::{self, VerifierQuery},
};
use crate::transcript::{read_n_points, read_n_scalars, Transcript};
use crate::rescue_transcript::RescueRead;

/// A verifier that checks a single proof at a time.
#[derive(Debug)]
pub struct MinimalSingleVerifier<'params> {
    msm: MSM<'params, EqAffine>,
}

impl<'params> MinimalSingleVerifier<'params> {
    fn process(
        self,
        f: impl FnOnce(
            MSM<'params, EqAffine>,
        ) -> Result<Guard<'params, EqAffine, Fp>, Error>,
    ) -> Result<(), Error> {
        let guard = f(self.msm)?;
        let msm = guard.use_challenges();
        if msm.eval() {
            Ok(())
        } else {
            Err(Error::ConstraintSystemFailure)
        }
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
    let num_proofs = 1;

    // Hash verification key into transcript
    vk.hash_into(transcript)?;

    let advice_commitments = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> {
            // Hash the prover's advice commitments into the transcript
            read_n_points(transcript, vk.cs.num_advice_columns)
        })
        .collect::<Result<Vec<_>, _>>()?;

    // Sample theta challenge for keeping lookup columns linearly independent
    // Even if we don't have lookups, we need to keep this in order to be consistent with the transcript
    let _theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();

    // Sample beta challenge
    let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();

    // Sample gamma challenge
    let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();

    let permutations_committed = (0..num_proofs)
        .map(|_| {
            // Hash each permutation product commitment
            vk.cs.permutation.read_product_commitments(vk, transcript)
        })
        .collect::<Result<Vec<_>, _>>()?;

    let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;

    // Sample y challenge, which keeps the gates linearly independent.
    let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();

    let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;

    // Sample x challenge, which is used to ensure the circuit is
    // satisfied with high probability.
    let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
    let instance_evals = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> { read_n_scalars(transcript, vk.cs.instance_queries.len()) })
        .collect::<Result<Vec<_>, _>>()?;

    let advice_evals = (0..num_proofs)
        .map(|_| -> Result<Vec<_>, _> { read_n_scalars(transcript, vk.cs.advice_queries.len()) })
        .collect::<Result<Vec<_>, _>>()?;

    let fixed_evals = read_n_scalars(transcript, vk.cs.fixed_queries.len())?;

    let vanishing = vanishing.evaluate_after_x(transcript)?;

    let permutations_common = vk.permutation.evaluate(transcript)?;

    let permutations_evaluated = permutations_committed
        .into_iter()
        .map(|permutation| permutation.evaluate(transcript))
        .collect::<Result<Vec<_>, _>>()?;

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
        let expressions = advice_evals
            .iter()
            .zip(instance_evals.iter())
            .zip(permutations_evaluated.iter())
            .flat_map(|((advice_evals, instance_evals), permutation)| {
                let fixed_evals = &fixed_evals;
                std::iter::empty()
                    // Evaluate the circuit using the custom gates provided
                    .chain(vk.cs.gates.iter().flat_map(move |gate| {
                        gate.polynomials().iter().map(move |poly| {
                            poly.evaluate(
                                &|scalar| scalar,
                                &|_| panic!("virtual selectors are removed during optimization"),
                                &|query| fixed_evals[query.index],
                                &|query| advice_evals[query.index],
                                &|query| instance_evals[query.index],
                                &|a| -a,
                                &|a, b| a + &b,
                                &|a, b| a * &b,
                                &|a, scalar| a * &scalar,
                            )
                        })
                    }))
                    .chain(permutation.expressions(
                        vk,
                        &vk.cs.permutation,
                        &permutations_common,
                        advice_evals,
                        fixed_evals,
                        instance_evals,
                        l_0,
                        l_last,
                        l_blind,
                        beta,
                        gamma,
                        x,
                    ))
            });

        vanishing.verify(params, expressions, y, xn)
    };

    let queries = advice_commitments
        .iter()
        .zip(advice_evals.iter())
        .zip(permutations_evaluated.iter())
        .flat_map(|((advice_commitments, advice_evals), permutation)| {
            iter::empty()
                .chain(vk.cs.advice_queries.iter().enumerate().map(
                    move |(query_index, &(column, at))| {
                        VerifierQuery::new_commitment(
                            &advice_commitments[column.index()],
                            vk.domain.rotate_omega(*x, at),
                            advice_evals[query_index],
                        )
                    },
                ))
                .chain(permutation.queries(vk, x))
        })
        .chain(
            vk.cs
                .fixed_queries
                .iter()
                .enumerate()
                .map(|(query_index, &(column, at))| {
                    VerifierQuery::new_commitment(
                        &vk.fixed_commitments[column.index()],
                        vk.domain.rotate_omega(*x, at),
                        fixed_evals[query_index],
                    )
                }),
        )
        .chain(permutations_common.queries(&vk.permutation, x))
        .chain(vanishing.queries(x));

    // We are now convinced the circuit is satisfied so long as the
    // polynomial commitments open to the correct values.
    strategy.process(|msm| {
        multiopen::verify_proof(params, transcript, queries, msm).map_err(|_| Error::Opening)
    })
}
