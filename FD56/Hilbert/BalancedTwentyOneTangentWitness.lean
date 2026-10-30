/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight21 seed with degree10/11 columns and
verified bounded-kernel tests at degrees5 and6. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedTwentyOneTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentU (R:=R) i).natDegree≤10 := by
  have hl : ∀i:Fin 5,(balancedTwentyOneTangentUData i).length≤11 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyOneTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedTwentyOneTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentV (R:=R) i).natDegree≤11 := by
  have hl : ∀i:Fin 5,(balancedTwentyOneTangentVData i).length≤12 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedTwentyOneTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedTwentyOneTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyOneTangentWitness (R:=K)) 5 balancedTwentyOneTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 6) ≃ Fin 60 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedTwentyOneTangentWitness (R:=K))
    5 balancedTwentyOneTangentCoefficientRows
  have he : M=(balancedTwentyOneTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedTwentyOneTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedTwentyOneTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyOneTangentWitness 5 balancedTwentyOneTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedTwentyOneTangent_selected_binding]
  exact balancedTwentyOneTangentSelected_injective

theorem balancedTwentyOneTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedTwentyOneTangentWitness (R:=K)) 5 balancedTwentyOneTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedTwentyOneTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyOneTangent_selected_integer_binding, balancedTwentyOneTangent_selected_binding]
  exact balancedTwentyOneTangentSelected_injective

theorem balancedTwentyOneTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedTwentyOneTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedTwentyOneTangentWitness 5 balancedTwentyOneTangentCoefficientRows
      balancedTwentyOneTangent_coefficient_injective_charZero v hv hdeg


theorem balancedTwentyOneTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyOneTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyOneTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyOneTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentU (R:=R) i).coeff 10=(![1,0,1,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyOneTangentUData j).getD 10 0=
      (![1,0,1,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyOneTangentUData i) : R[X]).coeff 10=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyOneTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyOneTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyOneTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyOneTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedTwentyOneTangentV (R:=R) i).coeff 11=(![0,0,-1,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedTwentyOneTangentVData j).getD 11 0=
      (![0,0,-1,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedTwentyOneTangentVData i) : R[X]).coeff 11=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedTwentyOneTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedTwentyOneTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedTwentyOneTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedTwentyOneTangentCritical_selected_integer_binding,
    balancedTwentyOneTangentCritical_selected_binding]
  exact balancedTwentyOneTangentCriticalSelected_injective

theorem balancedTwentyOneTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    63 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedTwentyOneTangentWitness (R:=K)) 6
        balancedTwentyOneTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedTwentyOneTangentWitness (R:=K)) 6
    balancedTwentyOneTangentCriticalCoefficientRows
  let select : Fin 63 → Fin 10 × Fin 7 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 7 ≃ Fin 70).symm (balancedTwentyOneTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedTwentyOneTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 63) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedTwentyOneTangent_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedTwentyOneTangentWitness (R:=K)) 6)≤7 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedTwentyOneTangentWitness (R:=K)) 6 balancedTwentyOneTangentCriticalCoefficientRows
  have hr := balancedTwentyOneTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
