/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.AffineSpecialization
import FD56.Hilbert.BetaCoefficients

/-! Maximal rank of the weighted beta equations transfers from affine witnesses
to the universal affine pair. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_beta_coefficient_injective_of_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hi : Function.Injective (betaCoefficientMatrix M P d).mulVec) :
    Function.Injective (betaCoefficientMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) d).mulVec := by
  let ψ := affinePairSpecialization M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  have hg : (betaCoefficientMatrix (universalAffineSquare K n m)
      (universalAffineRows K n m) d).map φ =
      betaCoefficientMatrix (genericAffineSquare K n m) (genericAffineRows K n m) d := by
    rw [← betaCoefficientMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  rw [← hg]
  apply matrix_injective_of_specialization MvPolynomial.C ψ
    (fun c => affinePairSpecialization_C M P c) φ (IsFractionRing.injective _ _)
  rw [← betaCoefficientMatrix_map, universalAffineSquare_pair_specialization M P hM,
    universalAffineRows_pair_specialization M P hP]
  exact hi

theorem generic_beta_coefficient_surjective_of_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hs : Function.Surjective (betaCoefficientMatrix M P d).mulVec) :
    Function.Surjective (betaCoefficientMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) d).mulVec := by
  let ψ := affinePairSpecialization M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  have hg : (betaCoefficientMatrix (universalAffineSquare K n m)
      (universalAffineRows K n m) d).map φ =
      betaCoefficientMatrix (genericAffineSquare K n m) (genericAffineRows K n m) d := by
    rw [← betaCoefficientMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  rw [← hg]
  apply matrix_surjective_of_specialization MvPolynomial.C ψ
    (fun c => affinePairSpecialization_C M P c) φ (IsFractionRing.injective _ _)
  rw [← betaCoefficientMatrix_map, universalAffineSquare_pair_specialization M P hM,
    universalAffineRows_pair_specialization M P hP]
  exact hs

theorem generic_beta_hilbert_of_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (d : ℕ)
    (hw : Module.finrank K (boundedBetaKernel M P d) =
      Fintype.card m * (2 * d + 3) - Fintype.card n * (d + 3)) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedBetaKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) =
      Fintype.card m * (2 * d + 3) - Fintype.card n * (d + 3) := by
  by_cases hd : Fintype.card m * (2 * d + 3) ≤ Fintype.card n * (d + 3)
  · have hi := beta_coefficient_injective_of_kernel_zero M P hM hP d
      (hw.trans (Nat.sub_eq_zero_of_le hd))
    have hgi := generic_beta_coefficient_injective_of_witness M P hM hP d hi
    rw [beta_kernel_finrank_of_coefficient_injective _ _
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) d hgi,
      Nat.sub_eq_zero_of_le hd]
  · have hs : Function.Surjective (betaCoefficientMatrix M P d).mulVec := by
      apply beta_coefficient_surjective_of_kernel_finrank M P hM hP d
      rw [hw]
      have hc := Nat.sub_add_cancel (show Fintype.card n * (d + 3) ≤
        Fintype.card m * (2 * d + 3) by omega)
      nlinarith
    have hgs := generic_beta_coefficient_surjective_of_witness M P hM hP d hs
    rw [beta_kernel_finrank_of_coefficient_surjective _ _
      (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) d hgs]
    congr 1
    ring
end FD56
