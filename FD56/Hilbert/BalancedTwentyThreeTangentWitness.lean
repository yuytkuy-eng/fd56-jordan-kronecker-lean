/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight23 seed with degree11/12 columns and
verified bounded-kernel tests at degrees5 and6. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedTwentyThreeTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentU (R:=R) i).natDegree≤11 := by
  have hl : ∀i:Fin 5,(balancedTwentyThreeTangentUData i).length≤12 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyThreeTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedTwentyThreeTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentV (R:=R) i).natDegree≤12 := by
  have hl : ∀i:Fin 5,(balancedTwentyThreeTangentVData i).length≤13 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyThreeTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedTwentyThreeTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyThreeTangentWitness (R:=K)) 5 balancedTwentyThreeTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 6) ≃ Fin 60 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedTwentyThreeTangentWitness (R:=K))
    5 balancedTwentyThreeTangentCoefficientRows
  have he : M=(balancedTwentyThreeTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedTwentyThreeTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedTwentyThreeTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyThreeTangentWitness 5 balancedTwentyThreeTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedTwentyThreeTangent_selected_binding]
  exact balancedTwentyThreeTangentSelected_injective

theorem balancedTwentyThreeTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyThreeTangentWitness (R:=K)) 5 balancedTwentyThreeTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedTwentyThreeTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyThreeTangent_selected_integer_binding, balancedTwentyThreeTangent_selected_binding]
  exact balancedTwentyThreeTangentSelected_injective

theorem balancedTwentyThreeTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedTwentyThreeTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyThreeTangentWitness 5 balancedTwentyThreeTangentCoefficientRows
      balancedTwentyThreeTangent_coefficient_injective_charZero v hv hdeg


theorem balancedTwentyThreeTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyThreeTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyThreeTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyThreeTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentU (R:=R) i).coeff 11=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyThreeTangentUData j).getD 11 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyThreeTangentUData i) : R[X]).coeff 11=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyThreeTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyThreeTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyThreeTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyThreeTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyThreeTangentV (R:=R) i).coeff 12=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyThreeTangentVData j).getD 12 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyThreeTangentVData i) : R[X]).coeff 12=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyThreeTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedTwentyThreeTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedTwentyThreeTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyThreeTangentCritical_selected_integer_binding,
    balancedTwentyThreeTangentCritical_selected_binding]
  exact balancedTwentyThreeTangentCriticalSelected_injective

theorem balancedTwentyThreeTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    67 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedTwentyThreeTangentWitness (R:=K)) 6
        balancedTwentyThreeTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedTwentyThreeTangentWitness (R:=K)) 6
    balancedTwentyThreeTangentCriticalCoefficientRows
  let select : Fin 67 → Fin 10 × Fin 7 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyThreeTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedTwentyThreeTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 67) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedTwentyThreeTangent_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedTwentyThreeTangentWitness (R:=K)) 6)≤3 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedTwentyThreeTangentWitness (R:=K)) 6 balancedTwentyThreeTangentCriticalCoefficientRows
  have hr := balancedTwentyThreeTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
