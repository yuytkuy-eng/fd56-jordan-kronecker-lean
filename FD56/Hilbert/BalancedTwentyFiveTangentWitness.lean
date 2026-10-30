/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight25 seed with degree12/13 columns and
verified bounded-kernel tests at degrees6 and7. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedTwentyFiveTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentU (R:=R) i).natDegree≤12 := by
  have hl : ∀i:Fin 5,(balancedTwentyFiveTangentUData i).length≤13 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyFiveTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedTwentyFiveTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentV (R:=R) i).natDegree≤13 := by
  have hl : ∀i:Fin 5,(balancedTwentyFiveTangentVData i).length≤14 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyFiveTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedTwentyFiveTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyFiveTangentWitness (R:=K)) 6 balancedTwentyFiveTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 7) ≃ Fin 70 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedTwentyFiveTangentWitness (R:=K))
    6 balancedTwentyFiveTangentCoefficientRows
  have he : M=(balancedTwentyFiveTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedTwentyFiveTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedTwentyFiveTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤6) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyFiveTangentWitness 6 balancedTwentyFiveTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedTwentyFiveTangent_selected_binding]
  exact balancedTwentyFiveTangentSelected_injective

theorem balancedTwentyFiveTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyFiveTangentWitness (R:=K)) 6 balancedTwentyFiveTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedTwentyFiveTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyFiveTangent_selected_integer_binding, balancedTwentyFiveTangent_selected_binding]
  exact balancedTwentyFiveTangentSelected_injective

theorem balancedTwentyFiveTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedTwentyFiveTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤6) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyFiveTangentWitness 6 balancedTwentyFiveTangentCoefficientRows
      balancedTwentyFiveTangent_coefficient_injective_charZero v hv hdeg


theorem balancedTwentyFiveTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyFiveTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyFiveTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyFiveTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentU (R:=R) i).coeff 12=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyFiveTangentUData j).getD 12 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyFiveTangentUData i) : R[X]).coeff 12=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyFiveTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyFiveTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyFiveTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyFiveTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyFiveTangentV (R:=R) i).coeff 13=(![0,-1,0,0,1] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyFiveTangentVData j).getD 13 0=
      (![0,-1,0,0,1] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyFiveTangentVData i) : R[X]).coeff 13=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyFiveTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedTwentyFiveTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedTwentyFiveTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyFiveTangentCritical_selected_integer_binding,
    balancedTwentyFiveTangentCritical_selected_binding]
  exact balancedTwentyFiveTangentCriticalSelected_injective

theorem balancedTwentyFiveTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    74 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedTwentyFiveTangentWitness (R:=K)) 7
        balancedTwentyFiveTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedTwentyFiveTangentWitness (R:=K)) 7
    balancedTwentyFiveTangentCriticalCoefficientRows
  let select : Fin 74 → Fin 10 × Fin 8 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 8 ≃ Fin 80).symm (balancedTwentyFiveTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedTwentyFiveTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 74) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedTwentyFiveTangent_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedTwentyFiveTangentWitness (R:=K)) 7)≤6 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedTwentyFiveTangentWitness (R:=K)) 7 balancedTwentyFiveTangentCriticalCoefficientRows
  have hr := balancedTwentyFiveTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
