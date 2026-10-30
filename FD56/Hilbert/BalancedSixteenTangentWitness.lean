/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSixteenTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight16 seed with degree8/8 columns and two verified
bounded-kernel tests at degrees3 and4. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedSixteenTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentU (R:=R) i).natDegree≤8 := by
  have hl : ∀i:Fin 5,(balancedSixteenTangentUData i).length≤9 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedSixteenTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedSixteenTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentV (R:=R) i).natDegree≤8 := by
  have hl : ∀i:Fin 5,(balancedSixteenTangentVData i).length≤9 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedSixteenTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedSixteenTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedSixteenTangentWitness (R:=K)) 3 balancedSixteenTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 4) ≃ Fin 40 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedSixteenTangentWitness (R:=K))
    3 balancedSixteenTangentCoefficientRows
  have he : M=(balancedSixteenTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedSixteenTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedSixteenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedSixteenTangentWitness 3 balancedSixteenTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedSixteenTangent_selected_binding]
  exact balancedSixteenTangentSelected_injective

theorem balancedSixteenTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedSixteenTangentWitness (R:=K)) 3 balancedSixteenTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedSixteenTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedSixteenTangent_selected_integer_binding, balancedSixteenTangent_selected_binding]
  exact balancedSixteenTangentSelected_injective

theorem balancedSixteenTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedSixteenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedSixteenTangentWitness 3 balancedSixteenTangentCoefficientRows
      balancedSixteenTangent_coefficient_injective_charZero v hv hdeg


theorem balancedSixteenTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSixteenTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSixteenTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSixteenTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentU (R:=R) i).coeff 8=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSixteenTangentUData j).getD 8 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSixteenTangentUData i) : R[X]).coeff 8=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSixteenTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSixteenTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSixteenTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSixteenTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSixteenTangentV (R:=R) i).coeff 8=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSixteenTangentVData j).getD 8 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSixteenTangentVData i) : R[X]).coeff 8=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSixteenTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedSixteenTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedSixteenTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedSixteenTangentCritical_selected_integer_binding,
    balancedSixteenTangentCritical_selected_binding]
  exact balancedSixteenTangentCriticalSelected_injective

theorem balancedSixteenTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    47 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedSixteenTangentWitness (R:=K)) 4
        balancedSixteenTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedSixteenTangentWitness (R:=K)) 4
    balancedSixteenTangentCriticalCoefficientRows
  let select : Fin 47 → Fin 10 × Fin 5 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSixteenTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedSixteenTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 47) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedSixteenTangent_kernel_finrank_four_le_three
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedSixteenTangentWitness (R:=K)) 4)≤3 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedSixteenTangentWitness (R:=K)) 4 balancedSixteenTangentCriticalCoefficientRows
  have hr := balancedSixteenTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
