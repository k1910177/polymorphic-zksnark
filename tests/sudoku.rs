#![warn(unused)]
#![deny(
    trivial_casts,
    trivial_numeric_casts,
    variant_size_differences,
    stable_features,
    non_shorthand_field_patterns,
    renamed_and_removed_lints,
    unsafe_code
)]

use ark_bls12_377::{Bls12_377, Fr};
use ark_ff::Field;
use ark_groth16::data_structures::{CircuitSpecificSetupPolymorphicSNARK, PolymorphicSNARK};
use ark_r1cs_std::{
    prelude::{AllocVar, AllocationMode, Boolean, EqGadget},
    uint8::UInt8,
};
use ark_relations::r1cs::{ConstraintSynthesizer, ConstraintSystemRef, Namespace, SynthesisError};
use ark_std::rand::{RngCore, SeedableRng};
use ark_std::test_rng;

use std::borrow::Borrow;

use cmp::CmpGadget;
mod cmp;

pub struct Sudoku<const N: usize, ConstraintF: Field>([[UInt8<ConstraintF>; N]; N]);
pub struct Solution<const N: usize, ConstraintF: Field>([[UInt8<ConstraintF>; N]; N]);

impl<const N: usize, F: Field> AllocVar<[[u8; N]; N], F> for Sudoku<N, F> {
    fn new_variable<T: Borrow<[[u8; N]; N]>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into();
        let row = [(); N].map(|_| UInt8::constant(0));
        let mut puzzle = Sudoku([(); N].map(|_| row.clone()));
        let value = f().map_or([[0; N]; N], |f| *f.borrow());
        for (i, row) in value.into_iter().enumerate() {
            for (j, cell) in row.into_iter().enumerate() {
                puzzle.0[i][j] = UInt8::new_variable(cs.clone(), || Ok(cell), mode)?;
            }
        }
        Ok(puzzle)
    }
}

impl<const N: usize, F: Field> AllocVar<[[u8; N]; N], F> for Solution<N, F> {
    fn new_variable<T: Borrow<[[u8; N]; N]>>(
        cs: impl Into<Namespace<F>>,
        f: impl FnOnce() -> Result<T, SynthesisError>,
        mode: AllocationMode,
    ) -> Result<Self, SynthesisError> {
        let cs = cs.into();
        let row = [(); N].map(|_| UInt8::constant(0));
        let mut solution = Solution([(); N].map(|_| row.clone()));
        let value = f().map_or([[0; N]; N], |f| *f.borrow());
        for (i, row) in value.into_iter().enumerate() {
            for (j, cell) in row.into_iter().enumerate() {
                solution.0[i][j] = UInt8::new_variable(cs.clone(), || Ok(cell), mode)?;
            }
        }
        Ok(solution)
    }
}

struct Puzzle<const N: usize> {
    sudoku: Option<[[u8; N]; N]>,
    solution: Option<[[u8; N]; N]>,
}

fn check_rows<const N: usize, ConstraintF: Field>(
    solution: &Solution<N, ConstraintF>,
) -> Result<(), SynthesisError> {
    for row in &solution.0 {
        for (j, cell) in row.iter().enumerate() {
            for prev in &row[0..j] {
                cell.is_neq(&prev)?.enforce_equal(&Boolean::TRUE)?;
            }
        }
    }
    Ok(())
}

fn check_cols<const N: usize, ConstraintF: Field>(
    solution: &Solution<N, ConstraintF>,
) -> Result<(), SynthesisError> {
    let mut transpose: Vec<Vec<UInt8<ConstraintF>>> = Vec::with_capacity(N * N);
    for i in 0..9 {
        let col = &solution
            .0
            .clone()
            .into_iter()
            .map(|s| s.into_iter().nth(i).unwrap())
            .collect::<Vec<UInt8<ConstraintF>>>();
        transpose.push(col.to_vec());
    }
    for row in transpose {
        for (j, cell) in row.iter().enumerate() {
            for prev in &row[0..j] {
                cell.is_neq(&prev)?.enforce_equal(&Boolean::TRUE)?;
            }
        }
    }
    Ok(())
}

fn check_3_by_3<const N: usize, ConstraintF: Field>(
    solution: &Solution<N, ConstraintF>,
) -> Result<(), SynthesisError> {
    let mut flat: Vec<UInt8<ConstraintF>> = Vec::with_capacity(N * N);
    for i in 0..3 {
        for j in 0..3 {
            flat.push(solution.0[i][j].clone());
        }
    }
    for (j, cell) in flat.iter().enumerate() {
        for prev in &flat[0..j] {
            cell.is_neq(&prev)?.enforce_equal(&Boolean::TRUE)?;
        }
    }
    Ok(())
}

fn check_sudoku_solution<const N: usize, ConstraintF: Field>(
    sudoku: &Sudoku<N, ConstraintF>,
    solution: &Solution<N, ConstraintF>,
) -> Result<(), SynthesisError> {
    for i in 0..9 {
        for j in 0..9 {
            let a = &sudoku.0[i][j];
            let b = &solution.0[i][j];
            (a.is_eq(b)?.or(&a.is_eq(&UInt8::constant(0))?)?).enforce_equal(&Boolean::TRUE)?;

            b.is_leq(&UInt8::constant(N as u8))?
                .and(&b.is_geq(&UInt8::constant(1))?)?
                .enforce_equal(&Boolean::TRUE)?;
        }
    }
    Ok(())
}

impl<const N: usize, F: Field> ConstraintSynthesizer<F> for Puzzle<N> {
    fn generate_constraints(self, cs: ConstraintSystemRef<F>) -> Result<(), SynthesisError> {
        let sudoku = self.sudoku;
        let solution = self.solution;

        let sudoku_var = Sudoku::new_input(cs.clone(), || {
            sudoku.ok_or(SynthesisError::AssignmentMissing)
        })?;
        let solution_var = Solution::new_witness(cs.clone(), || {
            solution.ok_or(SynthesisError::AssignmentMissing)
        })?;

        check_sudoku_solution(&sudoku_var, &solution_var)?;
        check_rows(&solution_var)?;
        check_cols(&solution_var)?;
        check_3_by_3(&solution_var)?;
        Ok(())
    }
}

fn flatten_input(sudoku: &[[u8; 9]; 9]) -> Vec<Fr>{
    let mut flat = Vec::new();
    for row in 0..9 {
        for col in 0..9 {
            let mut values = [Fr::from(0); 8];
            values.iter_mut().enumerate().for_each(|(i, v)| {
                *v = if (sudoku[row][col] >> i) & 1 == 1 {
                    Fr::from(1)
                } else {
                    Fr::from(0)
                }
            });
            flat.append(&mut values.to_vec())
        }
    }
    flat
}

#[test]
fn test_sudoku() {
    // We're going to use the Groth16 proving system.
    use ark_groth16::Groth16;

    // This may not be cryptographically safe, use
    // `OsRng` (for example) in production software.
    let mut rng = ark_std::rand::rngs::StdRng::seed_from_u64(test_rng().next_u64());

    // setup
    let (pk, vk) = {
        let c = Puzzle::<9> {
            sudoku: None,
            solution: None,
        };
        Groth16::<Bls12_377>::setup(c, &mut rng).unwrap()
    };
    let pvk = Groth16::<Bls12_377>::process_vk(&vk).unwrap();

    // rndgen
    let rnd = Groth16::<Bls12_377>::rndgen(&pk, &mut rng).unwrap();

    let sudoku = [
        [4, 5, 2, 6, 7, 8, 3, 1, 9],
        [8, 7, 3, 1, 0, 9, 4, 0, 6],
        [1, 9, 6, 3, 4, 0, 8, 7, 0],
        [6, 1, 5, 4, 9, 7, 2, 8, 3],
        [2, 3, 8, 5, 1, 6, 7, 9, 4],
        [9, 4, 7, 2, 8, 3, 5, 6, 1],
        [5, 2, 1, 7, 6, 4, 9, 3, 8],
        [3, 8, 4, 9, 0, 1, 6, 0, 7],
        [7, 6, 9, 8, 3, 0, 1, 4, 0],
    ];
    let solutions = [
        [
            [4, 5, 2, 6, 7, 8, 3, 1, 9],
            [8, 7, 3, 1, 5, 9, 4, 2, 6],
            [1, 9, 6, 3, 4, 2, 8, 7, 5],
            [6, 1, 5, 4, 9, 7, 2, 8, 3],
            [2, 3, 8, 5, 1, 6, 7, 9, 4],
            [9, 4, 7, 2, 8, 3, 5, 6, 1],
            [5, 2, 1, 7, 6, 4, 9, 3, 8],
            [3, 8, 4, 9, 2, 1, 6, 5, 7],
            [7, 6, 9, 8, 3, 5, 1, 4, 2],
        ],
        [
            [4, 5, 2, 6, 7, 8, 3, 1, 9],
            [8, 7, 3, 1, 2, 9, 4, 5, 6],
            [1, 9, 6, 3, 4, 5, 8, 7, 2],
            [6, 1, 5, 4, 9, 7, 2, 8, 3],
            [2, 3, 8, 5, 1, 6, 7, 9, 4],
            [9, 4, 7, 2, 8, 3, 5, 6, 1],
            [5, 2, 1, 7, 6, 4, 9, 3, 8],
            [3, 8, 4, 9, 5, 1, 6, 2, 7],
            [7, 6, 9, 8, 3, 2, 1, 4, 5],
        ],
    ];

    // prove
    let mut proofs = Vec::new();
    for (_, solution) in solutions.iter().enumerate() {
        let puzzle = Puzzle::<9> {
            sudoku: Some(sudoku),
            solution: Some(solution.clone()),
        };
        let proof = Groth16::<Bls12_377>::prove(&pk, puzzle, &rnd).unwrap();
        println!("{:?}", proof);
        println!("");
        proofs.push(proof);
    }

    // verify
    let flat = flatten_input(&sudoku);
    for (_, proof) in proofs.iter().enumerate() {
        assert!(Groth16::<Bls12_377>::verify_with_processed_vk(&pvk, &flat, &proof, &rnd).unwrap());
    }
    assert!(Groth16::<Bls12_377>::verify_all_proofs(&proofs).unwrap());
}
