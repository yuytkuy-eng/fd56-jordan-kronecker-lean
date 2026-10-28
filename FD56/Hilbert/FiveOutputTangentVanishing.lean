/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputTangentBinding
import FD56.Hilbert.FiveOutputTangentRank
import FD56.LinearAlgebra.RankSpecializationExtension

/-! The explicit tangent witness has no nonzero polynomial kernel vector
of degree at most five. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem fiveOutputTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (fiveOutputTangentU (R:=R) i).natDegree≤10 := by
  have hl : ∀i:Fin 5,(fiveOutputTangentUData i).length≤11 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (fiveOutputTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem fiveOutputTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (fiveOutputTangentV (R:=R) i).natDegree≤11 := by
  have hl : ∀i:Fin 5,(fiveOutputTangentVData i).length≤12 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (fiveOutputTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (fiveOutputTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (fiveOutputTangentWitness (R:=K)) 5 fiveOutputTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 6) ≃ Fin 60 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (fiveOutputTangentWitness (R:=K))
    5 fiveOutputTangentCoefficientRows
  have he : M=(fiveOutputTangentSelectedCoefficient (K:=K)).submatrix id e := by
    funext i j
    change M i j=M i (e.symm (e j))
    rw [Equiv.symm_apply_apply]
  change Function.Injective M.mulVec
  have hM : Function.Injective M.mulVec := by
    rw [he]
    intro x y hxy
    simp only [Matrix.submatrix_mulVec_equiv,Function.comp_id] at hxy
    have h := hinj hxy
    funext j
    simpa only [Function.comp_apply,Equiv.symm_apply_apply] using congrFun h (e j)
  exact hM

theorem fiveOutputTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : fiveOutputTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    fiveOutputTangentWitness 5 fiveOutputTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [fiveOutputTangent_selected_binding]
  exact fiveOutputTangentSelected_injective

theorem fiveOutputTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (fiveOutputTangentWitness (R:=K)) 5 fiveOutputTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [fiveOutputTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← fiveOutputTangent_selected_integer_binding, fiveOutputTangent_selected_binding]
  exact fiveOutputTangentSelected_injective

theorem fiveOutputTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : fiveOutputTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    fiveOutputTangentWitness 5 fiveOutputTangentCoefficientRows
      fiveOutputTangent_coefficient_injective_charZero v hv hdeg

end FD56
