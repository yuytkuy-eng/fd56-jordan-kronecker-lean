/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.DepthThreeDeformation

/-! A third-stack witness without a simultaneous-lifting capacity restriction. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

abbrev DepthThreeAlphaField (K n m : Type*) [Field K] :=
  FractionRing (DepthThreeStackField K n m)[X]

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

set_option maxHeartbeats 2000000 in
theorem exists_depth_three_alpha_full_witness
    (hmn : 3*Fintype.card m < Fintype.card n) :
    ∃ (M : Matrix n n (DepthThreeAlphaField K n m)[X])
      (P : Matrix m n (DepthThreeAlphaField K n m)[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
      ∀ d, Module.finrank (DepthThreeAlphaField K n m)
        (polynomialKernelAtDegree (observabilityMatrix M P 3) d) ≤
        (Fintype.card n-3*Fintype.card m)*(d+1)-6*Fintype.card m := by
  let F₀ := DepthThreeStackField K n m
  let L := DepthThreeAlphaField K n m
  let O := genericDepthThreePrefix K n m
  let P := O.submatrix Sum.inl id
  let Q := O.submatrix Sum.inr id
  let T := (genericDepthThreeStack K n m).submatrix Sum.inr id
  have h2 : 2*Fintype.card m < Fintype.card n := by omega
  have hO : depthTwoStack P Q=genericDepthThreePrefix K n m := by
    funext i j
    cases i <;> rfl
  have hfull : depthThreeStack P Q T=genericDepthThreeStack K n m := by
    funext i j
    rcases i with (i | i) | i <;> rfl
  have hb := genericDepthThreePrefix_basis_data (K := K) h2
  rw [← hO] at hb
  obtain ⟨B,a,hV,_,ha,_,hcard⟩ := hb
  have hright := genericDepthThreePrefix_right_inverse (K := K) h2
  rw [← hO] at hright
  obtain ⟨R,_,hR⟩ := hright
  have hP : DegreeBound P 1 := fun i j => genericDepthThreePrefix_degree (Sum.inl i) j
  have hQ : DegreeBound Q 2 := fun i j => genericDepthThreePrefix_degree (Sum.inr i) j
  have hT : DegreeBound T 3 := fun i j => genericPrescribedMatrix_degree _ (Sum.inr i) j
  have hlead : Function.Injective (Matrix.mulVec (fun x i =>
      (depthTwoStack P Q i x).coeff (depthTwoRowDegree i))) := by
    rw [hO]
    exact genericDepthThreePrefix_row_leading_injective (K := K) hmn.le
  have hrow := depthTwo_affine_coefficient_surjective P Q B R hR hP hQ hlead a hV hcard
  have hstack (j) : Function.Surjective
      (weightedCoefficientMatrix (depthTwoStack P Q) (fun _ => a j+1)
        (fun i => a j+1+depthTwoRowDegree i)).mulVec := by
    rw [hO]
    exact genericDepthThreePrefix_column_coefficient_surjective h2 a ha j
  let V := polynomialKernelBasisMatrix (depthTwoStack P Q) B
  have hTV : ∀ x j, ((T*V) x j).natDegree≤a j+3 := by
    intro x j
    simpa only [Nat.add_comm] using (matrixCoeff_mul_column T V 3 a hT hV x j).1
  obtain ⟨Mf,hMf,hzero,hFM⟩ := depthTwo_auxiliary_lift_of_coefficient_surjective
    P Q V a hP hQ hV hstack hrow (T*V) hTV
  obtain ⟨A,D,_,hfactor⟩ := depthTwo_affine_action_factor P Q B R hR hP hQ hlead Mf hMf hzero
  obtain ⟨M₀,hM₀,hM₀Q⟩ := depthTwo_affine_preimage_of_coefficient_surjective P Q hP hQ
    (genericDepthThreePrefix_first_coefficient_surjective (K := K) h2)
  let S := (Q*Mf-T)*R
  have hdiff : (Q*Mf-T)*V=0 := by rw [Matrix.sub_mul,hFM,sub_self]
  have hS : Q*Mf-T=S*depthTwoStack P Q :=
    row_factor_through_of_kernel_basis (depthTwoStack P Q) B R hR (Q*Mf-T) hdiff
  have hQM : Q*Mf=T+S*depthTwoStack P Q := by
    simpa only [add_comm] using sub_eq_iff_eq_add.mp hS
  let φ : F₀[X] →+* L := algebraMap F₀[X] L
  obtain ⟨M,P',hM,hP',hH⟩ := depthThree_deformed_witness φ (IsFractionRing.injective _ _)
    P Q T hP hQ hT Mf M₀ hMf hM₀ A D S hfactor hM₀Q hQM
  refine ⟨M,P',hM,hP',?_⟩
  intro d
  have hh := hH d
  rw [hfull,genericDepthThreeStack_hilbert hmn d] at hh
  exact hh

end FD56
