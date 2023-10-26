use ff::{Field, PrimeField};
use pasta_curves::{EqAffine, Fp};
use std::collections::BTreeMap;
use std::iter;
use std::ops::Mul;
use group::Curve;
use group::prime::PrimeCurveAffine;

use crate::{rescue_transcript::RescueRead, wrapper_ec::*};

use super::{
    ChallengeBeta, ChallengeGamma, ChallengeTheta, ChallengeX, ChallengeY, Error,
    VerifyingKey,
};
use crate::arithmetic::{lagrange_interpolate, eval_polynomial};
use crate::plonk::vanishing;
use crate::poly::multiopen::MinimalVerifierQuery;
use crate::poly::{commitment::Params, Rotation};
use crate::transcript::{Transcript, TranscriptRead, read_n_points, read_n_scalars};
use crate::poly::multiopen::Query;

/// Proof transcript. We also include the challenges for cross-checking which are not part of the
/// transcript since they can be computed by it. 
#[derive(Debug)]
pub struct MinimalVerifierTranscript {
    // transcript elements before multiopening
    vk_repr: Fp,
    advices_com: [EqAffine; 2],
    _theta: Fp,
    beta: Fp,
    gamma: Fp,
    permutation_z: [EqAffine; 3],
    vanishing_blinder: EqAffine,
    y: Fp,
    vanishing_h: [EqAffine; 2],
    x: Fp,
    _instance_evals: [Fp; 0], 
    advice_evals_at_x: [Fp; 2],
    advice_evals_at_omegax: [Fp; 1],
    fixed_evals_at_x: [Fp; 2],
    vanishing_blinder_eval: Fp,
    permutation_s_evals: [Fp; 3],
    permutation_z0_evals: [Fp; 3],
    permutation_z1_evals: [Fp; 3],
    permutation_z2_evals: [Fp; 2],
    // transcript elements at multiopening
    x_1: Fp,
    x_2: Fp,
    f_com: EqAffine,
    x_3: Fp,
    q_evals: [Fp; 3],
    x_4: Fp,
    // ipa poly com opening
    s: EqAffine,
    xi: Fp,
    z: Fp,
    crossterms_l: [EqAffine; 4],
    crossterms_r: [EqAffine; 4],
    u: [Fp; 4],
    c: Fp,
    f: Fp,
}

impl MinimalVerifierTranscript{
    /// parses the proof into a MinimalVerifierTranscript object
    pub fn parse_proof(
        params: &Params<EqAffine>,
        vk: &VerifyingKey<EqAffine>,
        transcript: &mut RescueRead<&[u8]>,
    ) -> Result<Self, Error> {

        // hash operation
        vk.hash_into(transcript)?;
        let vk_repr = vk.transcript_repr;

        // advice commitments
        let advices_com = read_n_points(transcript, vk.cs.num_advice_columns)?;
        assert_eq!(advices_com.len(), 2);
        let advices_com: [EqAffine; 2] = [advices_com[0], advices_com[1]];

        // challenge theta
        let _theta: ChallengeTheta<_> = transcript.squeeze_challenge_scalar();
        let _theta = _theta.inner;

        // challenge theta
        let beta: ChallengeBeta<_> = transcript.squeeze_challenge_scalar();
        let beta = beta.inner;

        // challenge gamma
        let gamma: ChallengeGamma<_> = transcript.squeeze_challenge_scalar();
        let gamma = gamma.inner;


        // permutation z commitments 
        let permutations_committed = vk.cs.permutation.read_product_commitments(vk, transcript)?;

        assert_eq!(permutations_committed.permutation_product_commitments.len(), 3);
        let permutation_z = [permutations_committed.permutation_product_commitments[0], permutations_committed.permutation_product_commitments[1], permutations_committed.permutation_product_commitments[2]];

        // vanishing blinder 
        let vanishing = vanishing::Argument::read_commitments_before_y(transcript)?;
        let vanishing_blinder = vanishing.random_poly_commitment;

        // challenge y
        let y: ChallengeY<_> = transcript.squeeze_challenge_scalar();
        let y = y.inner;

        // vanishing h polynomials 
        let vanishing = vanishing.read_commitments_after_y(vk, transcript)?;
        let vanishing_h = vanishing.h_commitments.clone();
        assert_eq!(vanishing_h.len(), 2);
        let vanishing_h = [vanishing_h[0], vanishing_h[1]];

        // challenge x
        let x: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let x = x.inner;


        // evaluations
        let advice_evals = read_n_scalars(transcript, vk.cs.advice_queries.len())?;
        assert_eq!(advice_evals.len(), 3);

        let advice_evals_at_x = [advice_evals[0], advice_evals[1]];
        let advice_evals_at_omegax = [advice_evals[2]];
        
        let fixed_evals = read_n_scalars(transcript, vk.cs.fixed_queries.len())?;
        assert_eq!(fixed_evals.len(), 2);
        let fixed_evals_at_x = [fixed_evals[0], fixed_evals[1]];

        // Random point to prove correctness of the random commitment of the vanishing polynomial
        let vanishing = vanishing.evaluate_after_x(transcript)?;
        let vanishing_blinder_eval = vanishing.random_eval;

        let permutations_common = vk.permutation.evaluate(transcript)?;

        let permutation_s_evals = permutations_common.permutation_evals;
        assert_eq!(permutation_s_evals.len(), 3);
        let permutation_s_evals = [permutation_s_evals[0], permutation_s_evals[1], permutation_s_evals[2]];

        let permutations_evaluated = permutations_committed.evaluate(transcript)?;
        // one set per permutation
        assert_eq!(permutations_evaluated.sets.len(), 3);

        // all apart from the last have an evaluation at omega^u x
        assert!(&permutations_evaluated.sets[0].permutation_product_last_eval.is_some());
        assert!(&permutations_evaluated.sets[1].permutation_product_last_eval.is_some());
        assert!(&permutations_evaluated.sets[2].permutation_product_last_eval.is_none());

        let permutation_z0_evals: [Fp; 3] = [
            permutations_evaluated.sets[0].permutation_product_eval,
            permutations_evaluated.sets[0].permutation_product_next_eval,
            permutations_evaluated.sets[0].permutation_product_last_eval.unwrap(),
        ];
        let permutation_z1_evals: [Fp; 3] = [
            permutations_evaluated.sets[1].permutation_product_eval,
            permutations_evaluated.sets[1].permutation_product_next_eval,
            permutations_evaluated.sets[1].permutation_product_last_eval.unwrap(),
        ];
        let permutation_z2_evals: [Fp; 2] = [
            permutations_evaluated.sets[2].permutation_product_eval,
            permutations_evaluated.sets[2].permutation_product_next_eval,
        ];

        // dummy challenge types, this is not important
        let x_1: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let x_1 = x_1.inner;

        let x_2: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let x_2 = x_2.inner;


        let f_com = transcript.read_point()?;

        let x_3: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let x_3 = x_3.inner;

        let q_evals = [transcript.read_scalar()?, transcript.read_scalar()?, transcript.read_scalar()?];

        let x_4: ChallengeX<_> = transcript.squeeze_challenge_scalar();
        let x_4 = x_4.inner;

        // ipa part 
        let s = transcript.read_point()?;

        let xi = *transcript.squeeze_challenge_scalar::<()>();
        let z = *transcript.squeeze_challenge_scalar::<()>();

        let k = params.k as usize;
        assert_eq!(k, 4);

        let mut crossterms_l: [EqAffine; 4] = [EqAffine::default(); 4];
        let mut crossterms_r: [EqAffine; 4] = [EqAffine::default(); 4];
        let mut u: [Fp; 4] = [Fp::default(); 4];
        for round in 0..k {
            // Read L and R from the proof and write them to the transcript
            crossterms_l[round] = transcript.read_point()?;
            crossterms_r[round] = transcript.read_point()?;
            u[round] = transcript.squeeze_challenge();
        }

        let c = transcript.read_scalar()?;
        let f = transcript.read_scalar()?;
        Ok(MinimalVerifierTranscript {
            vk_repr,
            advices_com,
            _theta,
            beta,
            gamma,
            permutation_z,
            vanishing_blinder,
            y,
            vanishing_h,
            x,
            _instance_evals: [], 
            advice_evals_at_x,
            advice_evals_at_omegax,
            fixed_evals_at_x,
            vanishing_blinder_eval,
            permutation_s_evals,
            permutation_z0_evals,
            permutation_z1_evals,
            permutation_z2_evals,
            x_1,
            x_2,
            f_com,
            x_3,
            q_evals,
            x_4,
            s,
            xi,
            z,
            crossterms_l,
            crossterms_r,
            u,
            c,
            f,
        })
    }
}

/// Returns a boolean indicating whether or not the proof is valid
pub fn minimal_verify_proof(
    params: &Params<EqAffine>,
    vk: &VerifyingKey<EqAffine>,
    _instances: &[&[&[Fp]]],
    transcript: &mut RescueRead<&[u8]>,
) -> Result<(), Error> {

    // read transcript. This is a witnessed part when verifying in circuit
    let minimal_transcript = MinimalVerifierTranscript::parse_proof( params, vk, &mut transcript.clone())?;

    // ======== HashOP: absorb vk_repr
    let _vk_repr = minimal_transcript.vk_repr;


    // read advice commitments (G1)
    // ======== HashOP: absorb 
    let advice_commitments = minimal_transcript.advices_com.to_vec();

    // ======== HashOp: squeze 
    let _theta = minimal_transcript._theta;
    // ======== HashOp: squeze 
    let beta = minimal_transcript.beta;
    // ======== HashOp: squeze 
    let gamma = minimal_transcript.gamma;

    // read commitments to z polynomials (G1)
    // ======== HashOP: absorb 
    let permutations_committed = minimal_transcript.permutation_z;

    // read the poly that blinds the vanishing polynomial (G1)
    // ======== HashOP: absorb 
    let vanishing_rand = minimal_transcript.vanishing_blinder;

    // ======== HashOp: squeze 
    let y = minimal_transcript.y;

    // read the h polynomials (G1)
    // ======== HashOP: absorb 
    let vanishing_split = minimal_transcript.vanishing_h;

    // ======== HashOp: squeze 
    let x = minimal_transcript.x;

    // We don't have instance evals
    // ======== HashOp: absorb if instance cols are used 
    let _instance_evals: [Fp; 0] = [];

    // read advice and fixed evaluations (Fp)
    // ======== HashOP: absorb 
    let advice_evals_at_x = minimal_transcript.advice_evals_at_x;
    // ======== HashOP: absorb 
    let advice_evals_at_omegax = minimal_transcript.advice_evals_at_omegax;
    // ======== HashOP: absorb 
    let fixed_evals_at_x = minimal_transcript.fixed_evals_at_x;
    
    // read blinder poly evaluation (Fp)
    // ======== HashOP: absorb 
    let random_eval = minimal_transcript.vanishing_blinder_eval;

    // read permutation evaluations (Fp)
    // ======== HashOP: absorb 
    let permutations_common_evals = minimal_transcript.permutation_s_evals; 



    // read z_poly evaluations (Fp)
    // ======== HashOP: absorb 
    let permutations_evaluated_a = (
        permutations_committed[0],
        minimal_transcript.permutation_z0_evals[0],
        minimal_transcript.permutation_z0_evals[1],
        minimal_transcript.permutation_z0_evals[2],
    );
    let permutations_evaluated_b = (
        permutations_committed[1],
        minimal_transcript.permutation_z1_evals[0],
        minimal_transcript.permutation_z1_evals[1],
        minimal_transcript.permutation_z1_evals[2],
    );
    let permutations_evaluated_c = (
        permutations_committed[2],
        minimal_transcript.permutation_z2_evals[0],
        minimal_transcript.permutation_z2_evals[1],
    );

    // This check ensures the circuit is satisfied so long as the polynomial
    // commitments open to the correct values.
    let vanishing = {
        // x^n
        // n is fixed. This would be an in-circuit field operation (x -> x^n)
        // First compute x^n
        // ======== Fq op ==> x -> x^n (x^{2^k} k doublings? More efficient implementation?)
        let xn = x.pow([params.n, 0, 0, 0]);

        // This is a fixed number when the circuit is fixed
        let blinding_factors = vk.cs.blinding_factors();

        // evaluation of lg polynomials
        // this are in-circut Fp operation
        // evaluation of lg polynomials at   
        //
        // ======== Fq op ==> x, i -> lg_i(x)
        //          We do this by asserting: yi (X-\omega_i) - ci(xn-1) = 0
        //          Here, yi is the claimed evaluation and ci, omega_i fixed constants
        let l_evals = vk
            .domain
            .l_i_range(x, xn, (-((blinding_factors + 1) as i32))..=0);


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
            *left *= &(col + &(beta * col_eval) + &gamma);

            let mut right = perm_eval;

            let current_delta =
                beta * x * &(Fp::DELTA
                    .pow_vartime([delta_power])); // chunk_len = 1
            right *= &(col + &current_delta + &gamma);

            (*left - &right) * (Fp::ONE - &(l_last + &l_blind))
        };



        // Compute the expected value of h(x)
        let expressions = {
            let _instance_evals = &_instance_evals; // No instance values in our example

            // We have only one gate, which we evaluate directly.
            // We have two evaluations of fixed columns, one for the fixed column (which we don't use
            // in the gate) and one for the selector (which we use here),
            // ======== Fq op ==> gate correctness 
            iter::once(fixed_evals_at_x[1] * (advice_evals_at_x[0] * advice_evals_at_x[1] - advice_evals_at_omegax[0]))
                // Now we work on the permutation argument
                // Enforce only for the first set.
                // l_0(X) * (1 - z_0(X)) = 0
                // CP1 in notes
                // ======== Fq op ==> permutation correctness 
                .chain(iter::once(l_0 * &(Fp::ONE - &permutations_evaluated_a.1)))
                // Next we enforce only for the last set.
                // l_last(X) * (z_l(X)^2 - z_l(X)) = 0
                // CP2 in notes
                // ======== Fq op ==> permutation correctness 
                .chain(iter::once(
                    &l_last * &(permutations_evaluated_c.1.square() - &permutations_evaluated_c.1),
                ))
                // Except for the first set, enforce.
                // l_0(X) * (z_i(X) - z_{i-1}(\omega^(last) X)) = 0
                // CP3 and CP4 in notes
                // ======== Fq op ==> permutation correctness 
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
                // ======== Fq op ==> permutation correctness 
                .chain(iter::once({
                    let mut left = permutations_evaluated_a.2;
                    last_permutation_constraint(fixed_evals_at_x[0], permutations_common_evals[0], permutations_evaluated_a.1, &mut left, 0)
                }))
                .chain(iter::once({
                    let mut left = permutations_evaluated_b.2;
                    last_permutation_constraint(advice_evals_at_x[0], permutations_common_evals[1], permutations_evaluated_b.1, &mut left, 1)
                }))
                .chain(iter::once({
                    let mut left = permutations_evaluated_c.2;
                    last_permutation_constraint(advice_evals_at_x[1], permutations_common_evals[2], permutations_evaluated_c.1, &mut left, 2)
                }))
        };

        // Now we compute the vanishing polynomial expected evaluation
        // These are in-circut field operations
        // ======== Fq op ==> combine results using y to get h_poly_eval
        let expected_h_eval = expressions.fold(Fp::ZERO, |h_eval, v| h_eval * &y + &v);
        let expected_h_eval = expected_h_eval * ((xn - Fp::ONE).invert().unwrap());

        // and its commitment
        // In circut ECC operation
        // h_1*x^n + h_0
        // ======== Fp op 
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
    // ======== Fq op  x -> \omega x
    let x_next = vk.domain.rotate_omega(x, Rotation::next());
    // ======== Fq op  x -> \omega^u x
    let x_last = vk
        .domain
        .rotate_omega(x, Rotation(-((blinding_factors + 1) as i32)));


    let advice_evals = [advice_evals_at_x[0], advice_evals_at_x[1], advice_evals_at_omegax[0]];


    // this gathers the necessary queries to open the polycoms later on
    let queries = {
        iter::empty()
            .chain(vk.cs.advice_queries.iter().enumerate().map(
                move |(query_index, &(column, at))| MinimalVerifierQuery {
                    point: vk.domain.rotate_omega(x, at),
                    commitment: advice_commitments[column.index()],
                    eval: advice_evals[query_index],
                },
            ))
            // Open permutation product commitments at x and \omega x
            .chain(Some(MinimalVerifierQuery {
                point: x,
                commitment: permutations_evaluated_a.0,
                eval: permutations_evaluated_a.1,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_next,
                commitment: permutations_evaluated_a.0,
                eval: permutations_evaluated_a.2,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x,
                commitment: permutations_evaluated_b.0,
                eval: permutations_evaluated_b.1,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x_next,
                commitment: permutations_evaluated_b.0,
                eval: permutations_evaluated_b.2,
            }))
            .chain(Some(MinimalVerifierQuery {
                point: x,
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
                    point: vk.domain.rotate_omega(x, at),
                    commitment: vk.fixed_commitments[column.index()],
                    eval: fixed_evals_at_x[query_index],
                }),
        )
        .chain(vk.permutation.commitments
            .iter()
            .zip(permutations_common_evals.iter())
            .map(move |(commitment, &eval)| MinimalVerifierQuery {
                point: x,
                commitment: *commitment,
                eval,
            }))
        .chain(Some(MinimalVerifierQuery {
            point: x,
            commitment: vanishing.0,
            eval: vanishing.1,
        }))
        .chain(Some(MinimalVerifierQuery {
            point: x,
            commitment: vanishing_rand,
            eval: random_eval,
        }));

    // ======== HashOP: squeeze 
    let x_1 = minimal_transcript.x_1;

    // ======== HashOP: squeeze 
    let x_2 = minimal_transcript.x_2;

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

    let mut evals = vec![Fp::ZERO; point_index_map.len()];

    // Now for each query we add the polynomial to its q aggregate polynomial (by multiplying always with a
    // different power of x_1), which is determined by it's evaluation point.
    // Computes linear combination of commitments
    // ======== Fp op:  \sum [q_i] x_1 ^ i
    // ======== Fq op:  \sum [q_i_claimed_eval] x_1 ^ i
    for query in queries.clone() {
        let q_comm_index = point_index_map[&query.get_point()];
        let q_commitment = &mut q_commitments[q_comm_index];
        *q_commitment = (q_commitment.mul(x_1) + query.get_commitment()).to_affine();

        evals[q_comm_index] *= x_1;
        evals[q_comm_index] += query.get_eval();
    }

    // read witness polynomial for aggregate opening
    // ======== HashOP: absorb 
    let q_prime_commitment = minimal_transcript.f_com;

    // ======== HashOP: squeeze 
    let x_3 = minimal_transcript.x_3;

    // ======== HashOP: absorb 
    let q_evals = minimal_transcript.q_evals;

    // We can compute the expected msm_eval at x_3 using the u provided
    // by the prover and from x_2
    let msm_eval = point_index_map
        .into_iter()
        .fold(Fp::ZERO, |msm_eval, (point, index)| {
            let r_poly = lagrange_interpolate(&[point], &[evals[index]]);
            let r_eval = eval_polynomial(&r_poly, x_3);
            let eval = (q_evals[index] - &r_eval) * &(x_3 - point).invert().unwrap();
            msm_eval * &(x_2) + &eval
        });
    
    // ======== HashOP: squeeze 
    let x_4 = minimal_transcript.x_4;



    // Compute P (the final commitment that has to be opened)
    // ======== Fp op:  \sum [q_i] x_4 ^ i
    let p = (q_prime_commitment.mul(x_4*x_4*x_4) 
        + q_commitments[0].mul(x_4*x_4)
        + q_commitments[1].mul(x_4)
        + q_commitments[2]).to_affine();

    // ======== Fq op:  \sum [q_i_claimed_eval] x_4 ^ i
    let v = msm_eval*x_4*x_4*x_4
        + q_evals[0]*x_4*x_4
        + q_evals[1]*x_4
        + q_evals[2];


    // at this point we have our commitment
    
    // IPA part
    let k = params.k as usize;

    // P' = P - [v] G_0 + [ξ] S
    let g_zero = params.g[0];
    let vg0 = mul(&v, &g_zero);
    let p_minus_vg0 = sub(&p, &vg0);

    let s_poly_commitment = minimal_transcript.s;
    let xi = minimal_transcript.xi;
    let xis = mul(&xi, &s_poly_commitment);
    let p_prime = add(&p_minus_vg0, &xis);

    let z = minimal_transcript.z;

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
        let l = minimal_transcript.crossterms_l[round];
        let r = minimal_transcript.crossterms_r[round];
        let u_j = minimal_transcript.u[round];

        // Half at vector at n / 2^(1 + round)
        let half = ((1 << k) / (1 << (round + 1))) as usize;
        let first_half = folded_gs[round][..half].to_vec();
        let mut second_half = folded_gs[round][half..].to_vec();
        second_half.iter_mut().for_each(|a| *a = mul(&u_j, a));

        folded_gs[round + 1] = first_half
            .iter()
            .zip(second_half.iter())
            .map(|(r, l)| add(r, l))
            .collect::<Vec<_>>();

        rounds.push((l, r, u_j, /* to be inverted */ u_j));
    }
    
    assert_eq!(folded_gs[k].len(), 1);

    rounds
        .iter_mut()
        .for_each(|(_, _, _, u)| *u = scalar_inversion(u));

    // P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    // This is the left-hand side of the verifier equation.
    let lhs = rounds.iter_mut().fold(p_prime, |p, (l, r, u, u_inv)| {
        let l_uinv = mul(u_inv, l);
        let r_u = mul(u, r);
        let sum = add(&r_u, &l_uinv);
        add(&p, &sum)
    });

    // Our goal is to check that the left hand side of the verifier
    // equation
    //     P' + \sum([u_j^{-1}] L_j) + \sum([u_j] R_j)
    // equals the right-hand side
    //   = [c] (G'_0 + [b * z] U) + [f] W

    let c = minimal_transcript.c;
    let f = minimal_transcript.f;

    let mut b = Fp::ONE;
    let mut cur_power = x_3;

    // Computes $\prod\limits_{i=0}^{k-1} (1 + u_{k - 1 - i} x^{2^i})$.
    for u_j in rounds.iter().rev().map(|(_, _, u_j, _)| u_j) {
        b *= Fp::ONE + &(*u_j * &cur_power);
        cur_power *= cur_power;
    }

    let mut rhs = EqAffine::identity();
    let u = params.u;
    let w = params.w;

    let scalar_u = scalar_product(&[c, b, z]);

    rhs = add(&rhs, &mul(&scalar_u, &u));
    rhs = add(&rhs, &mul(&f, &w));

    rhs = add(&rhs, &mul(&c, &folded_gs[k][0]));


    if lhs == rhs {
        Ok(())
    } else {
        Err(Error::Opening)
    }
}
