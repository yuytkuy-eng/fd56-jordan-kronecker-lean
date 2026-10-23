/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthTwoGenericStack
import FD56.Hilbert.DepthTwoDeformedWitness
import FD56.Hilbert.DepthTwoBetaKernel

/-! Affine depth-two witnesses attain every coefficient-dimension lower bound
for the second auxiliary kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

abbrev DepthTwoBetaWitnessField (K n m : Type*) [Field K] :=
  FractionRing (DepthTwoStackField K n m)[X]

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

set_option maxHeartbeats 2000000 in
theorem exists_depth_two_beta_witness
    (hmn : 2 * Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 3 * Fintype.card m) :
    ∃ (M : Matrix n n (DepthTwoBetaWitnessField K n m)[X])
      (P : Matrix m n (DepthTwoBetaWitnessField K n m)[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
      ∀ d, Module.finrank (DepthTwoBetaWitnessField K n m)
        (boundedDepthTwoBetaKernel M P d) ≤
        Fintype.card m * (3 * d + 6) - Fintype.card n * (d + 4) := by
  let F₀ := DepthTwoStackField K n m
  let L := DepthTwoBetaWitnessField K n m
  let O := genericDepthTwoStack K n m
  let P := O.submatrix Sum.inl id
  let Q := O.submatrix Sum.inr id
  have hO : depthTwoStack P Q = genericDepthTwoStack K n m := by funext i j; cases i <;> rfl
  have hb := genericDepthTwoStack_basis_data (K := K) hmn
  rw [← hO] at hb
  obtain ⟨B,a,hV,hVL,ha,hsum,hcard⟩ := hb
  have hright := genericDepthTwoStack_right_inverse (K := K) hmn
  rw [← hO] at hright
  obtain ⟨R,_,hR⟩ := hright
  have hP : DegreeBound P 1 := fun i j => genericPrescribedMatrix_degree _ (Sum.inl i) j
  have hQ : DegreeBound Q 2 := fun i j => genericPrescribedMatrix_degree _ (Sum.inr i) j
  have hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))) := by
    rw [hO]
    exact genericDepthTwoStack_row_leading_injective (K := K) hmn.le
  have hrow := depthTwo_affine_coefficient_surjective P Q B R hR hP hQ hlead a hV hcard
  have hstack (j) : Function.Surjective
      (weightedCoefficientMatrix (depthTwoStack P Q) (fun _ => a j + 1)
        (fun i => a j + 1 + depthTwoRowDegree i)).mulVec := by
    rw [hO]
    exact genericDepthTwoStack_column_coefficient_surjective hmn a ha j
  obtain ⟨F,hF,hFH⟩ := exists_prescribed_column_matrix_balanced_kernel
    (K := F₀) (a := m) (fun j => a j + 3) (by simp; omega)
  obtain ⟨Mf,hMf,hzero,hFM⟩ := depthTwo_auxiliary_lift_of_coefficient_surjective
    P Q (polynomialKernelBasisMatrix (depthTwoStack P Q) B) a hP hQ hV hstack hrow F hF
  obtain ⟨A,D,hA,hfactor⟩ := depthTwo_affine_action_factor P Q B R hR hP hQ hlead Mf hMf hzero
  obtain ⟨M₀,hM₀,hM₀Q⟩ := depthTwo_affine_preimage_of_coefficient_surjective P Q hP hQ
    (genericDepthTwoStack_first_coefficient_surjective (K := K) hmn)
  let φ : F₀[X] →+* L := algebraMap F₀[X] L
  obtain ⟨M,B',R',hM,hP',hR',hB',hlead',hH⟩ := depthTwo_deformed_witness
    φ (IsFractionRing.injective _ _) P Q B R hR hP hQ hlead a hV
    Mf M₀ hMf hM₀ A D hA hfactor hM₀Q hzero
  let P' := P.map (Polynomial.mapRingHom (φ.comp C))
  refine ⟨M,P',hM,hP',?_⟩
  intro d
  rw [depthTwo_beta_kernel_finrank M P' B' R' hR' hM hP' hlead' d]
  have hh := hH d
  rw [hFM,hFH] at hh
  have hpow : P' * M * M = P' * M ^ 2 := by rw [pow_two,Matrix.mul_assoc]
  rw [hpow]
  have hs : (∑ j, (a j + 3)) = 3 * Fintype.card m +
      3 * (Fintype.card n - 2 * Fintype.card m) := by
    simp only [Finset.sum_add_distrib,hsum,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    omega
  rw [Fintype.card_fin,hs] at hh
  have hnr : Fintype.card n = 2 * Fintype.card m +
      (Fintype.card n - 2 * Fintype.card m) := by omega
  have hms : Fintype.card m =
      (Fintype.card n - 2 * Fintype.card m) +
      (Fintype.card m - (Fintype.card n - 2 * Fintype.card m)) := by omega
  have hbalance : Fintype.card m * (3 * d + 6) +
      (3 * Fintype.card m + 3 * (Fintype.card n - 2 * Fintype.card m)) =
      Fintype.card n * (d + 4) +
      (Fintype.card m - (Fintype.card n - 2 * Fintype.card m)) * (d + 1) := by
    nlinarith
  exact hh.trans_eq (by omega)

end FD56
