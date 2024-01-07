use crate::Randomizer;
use crate::{r1cs_to_qap::R1CSToQAP, Groth16, Proof, ProvingKey};
use ark_ec::{pairing::Pairing, AffineRepr, CurveGroup, Group, VariableBaseMSM};
use ark_ff::{PrimeField, UniformRand, Zero};
use ark_poly::GeneralEvaluationDomain;
use ark_relations::r1cs::{
    ConstraintSynthesizer, ConstraintSystem, OptimizationGoal, Result as R1CSResult,
};
use ark_std::rand::Rng;
use ark_std::{
    cfg_into_iter, cfg_iter,
    ops::{AddAssign, Mul},
    vec::Vec,
};

#[cfg(feature = "parallel")]
use rayon::prelude::*;

type D<F> = GeneralEvaluationDomain<F>;

impl<E: Pairing, QAP: R1CSToQAP> Groth16<E, QAP> {
    /// Create randomizer
    #[inline]
    pub fn create_randomizer(pk: &ProvingKey<E>, rng: &mut impl Rng) -> R1CSResult<Randomizer<E>> {
        let r = E::ScalarField::rand(rng);
        let s = E::ScalarField::rand(rng);

        let s_delta_g1 = pk.delta_g1.into_group().mul_bigint(&s.into_bigint());
        let r_delta_g2 = pk.delta_g2.into_group().mul_bigint(&r.into_bigint());

        Ok(Randomizer {
            r,
            s,
            p: s_delta_g1.into_affine(),
            q: r_delta_g2.into_affine(),
        })
    }

    /// Create a Groth16 proof using randomness `r` and `s` and the provided
    /// R1CS-to-QAP reduction.
    #[inline]
    pub fn create_proof_with_reduction<C>(
        circuit: C,
        pk: &ProvingKey<E>,
        r: E::ScalarField,
        s: E::ScalarField,
    ) -> R1CSResult<Proof<E>>
    where
        E: Pairing,
        C: ConstraintSynthesizer<E::ScalarField>,
        QAP: R1CSToQAP,
    {
        let prover_time = start_timer!(|| "Groth16::Prover");
        let cs = ConstraintSystem::new_ref();

        // Set the optimization goal
        cs.set_optimization_goal(OptimizationGoal::Constraints);

        // Synthesize the circuit.
        let synthesis_time = start_timer!(|| "Constraint synthesis");
        circuit.generate_constraints(cs.clone())?;
        debug_assert!(cs.is_satisfied().unwrap());
        end_timer!(synthesis_time);

        let lc_time = start_timer!(|| "Inlining LCs");
        cs.finalize();
        end_timer!(lc_time);

        let witness_map_time = start_timer!(|| "R1CS to QAP witness map");
        let h = QAP::witness_map::<E::ScalarField, D<E::ScalarField>>(cs.clone())?;
        end_timer!(witness_map_time);

        let prover = cs.borrow().unwrap();
        let proof = Self::create_proof_with_assignment(
            pk,
            r,
            s,
            &h,
            &prover.instance_assignment[1..],
            &prover.witness_assignment,
        )?;

        end_timer!(prover_time);

        Ok(proof)
    }

    #[inline]
    fn create_proof_with_assignment(
        pk: &ProvingKey<E>,
        r: E::ScalarField,
        s: E::ScalarField,
        h: &[E::ScalarField],
        input_assignment: &[E::ScalarField],
        aux_assignment: &[E::ScalarField],
    ) -> R1CSResult<Proof<E>> {
        let c_acc_time = start_timer!(|| "Compute C");
        let h_assignment = cfg_into_iter!(h)
            .map(|s| s.into_bigint())
            .collect::<Vec<_>>();
        let h_acc = E::G1::msm_bigint(&pk.h_query, &h_assignment[..h_assignment.len() - 1]);
        drop(h_assignment);

        // Compute C
        let aux_assignment = cfg_iter!(aux_assignment)
            .map(|s| s.into_bigint())
            .collect::<Vec<_>>();

        let l_aux_acc = E::G1::msm_bigint(&pk.l_query, &aux_assignment);

        end_timer!(c_acc_time);

        let input_assignment = input_assignment
            .iter()
            .map(|s| s.into_bigint())
            .collect::<Vec<_>>();

        let assignment = [&input_assignment[..], &aux_assignment[..]].concat();
        drop(aux_assignment);

        // Compute A
        let a_acc_time = start_timer!(|| "Compute A");
        let r_g1 = pk.delta_g1.mul(r);

        let g_a = Self::calculate_coeff(r_g1, &pk.a_query, pk.vk.alpha_g1, &assignment);

        let s_g_a = g_a.mul_bigint(&s.into_bigint());
        end_timer!(a_acc_time);

        // Compute B in G1 if needed
        let g1_b = if !r.is_zero() {
            let b_g1_acc_time = start_timer!(|| "Compute B in G1");
            let s_g1 = pk.delta_g1.mul(s);
            let g1_b = Self::calculate_coeff(s_g1, &pk.b_g1_query, pk.beta_g1, &assignment);

            end_timer!(b_g1_acc_time);

            g1_b
        } else {
            E::G1::zero()
        };

        // Compute B in G2
        let b_g2_acc_time = start_timer!(|| "Compute B in G2");
        let s_g2 = pk.vk.delta_g2.mul(s);
        let g2_b = Self::calculate_coeff(s_g2, &pk.b_g2_query, pk.vk.beta_g2, &assignment);
        let r_g1_b = g1_b.mul_bigint(&r.into_bigint());
        drop(assignment);

        end_timer!(b_g2_acc_time);

        let c_time = start_timer!(|| "Finish C");
        let mut g_c = s_g_a;
        g_c += &r_g1_b;
        g_c += &l_aux_acc;
        g_c += &h_acc;
        end_timer!(c_time);

        Ok(Proof {
            a: g_a.into_affine(),
            b: g2_b.into_affine(),
            c: g_c.into_affine(),
        })
    }

    fn calculate_coeff<G: AffineRepr>(
        initial: G::Group,
        query: &[G],
        vk_param: G,
        assignment: &[<G::ScalarField as PrimeField>::BigInt],
    ) -> G::Group
    where
        G::Group: VariableBaseMSM<MulBase = G>,
    {
        let el = query[0];
        let acc = G::Group::msm_bigint(&query[1..], assignment);

        let mut res = initial;
        res.add_assign(&el);
        res += &acc;
        res.add_assign(&vk_param);

        res
    }
}
