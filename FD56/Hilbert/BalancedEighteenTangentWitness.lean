/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight18 seed with degree9/9 columns and
verified bounded-kernel tests at degrees4 and5. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedEighteenTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentU (R:=R) i).natDegree≤9 := by
  have hl : ∀i:Fin 5,(balancedEighteenTangentUData i).length≤10 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedEighteenTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedEighteenTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentV (R:=R) i).natDegree≤9 := by
  have hl : ∀i:Fin 5,(balancedEighteenTangentVData i).length≤10 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedEighteenTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedEighteenTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedEighteenTangentWitness (R:=K)) 4 balancedEighteenTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 5) ≃ Fin 50 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedEighteenTangentWitness (R:=K))
    4 balancedEighteenTangentCoefficientRows
  have he : M=(balancedEighteenTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedEighteenTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedEighteenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤4) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedEighteenTangentWitness 4 balancedEighteenTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedEighteenTangent_selected_binding]
  exact balancedEighteenTangentSelected_injective

theorem balancedEighteenTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedEighteenTangentWitness (R:=K)) 4 balancedEighteenTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedEighteenTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedEighteenTangent_selected_integer_binding, balancedEighteenTangent_selected_binding]
  exact balancedEighteenTangentSelected_injective

theorem balancedEighteenTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedEighteenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤4) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedEighteenTangentWitness 4 balancedEighteenTangentCoefficientRows
      balancedEighteenTangent_coefficient_injective_charZero v hv hdeg


theorem balancedEighteenTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedEighteenTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedEighteenTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedEighteenTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentU (R:=R) i).coeff 9=(![1,1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedEighteenTangentUData j).getD 9 0=
      (![1,1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedEighteenTangentUData i) : R[X]).coeff 9=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedEighteenTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedEighteenTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedEighteenTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedEighteenTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedEighteenTangentV (R:=R) i).coeff 9=(![0,0,0,0,1] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedEighteenTangentVData j).getD 9 0=
      (![0,0,0,0,1] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedEighteenTangentVData i) : R[X]).coeff 9=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedEighteenTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedEighteenTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedEighteenTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedEighteenTangentCritical_selected_integer_binding,
    balancedEighteenTangentCritical_selected_binding]
  exact balancedEighteenTangentCriticalSelected_injective

theorem balancedEighteenTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    54 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedEighteenTangentWitness (R:=K)) 5
        balancedEighteenTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedEighteenTangentWitness (R:=K)) 5
    balancedEighteenTangentCriticalCoefficientRows
  let select : Fin 54 → Fin 10 × Fin 6 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 6 ≃ Fin 60).symm (balancedEighteenTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedEighteenTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 54) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedEighteenTangent_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedEighteenTangentWitness (R:=K)) 5)≤6 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedEighteenTangentWitness (R:=K)) 5 balancedEighteenTangentCriticalCoefficientRows
  have hr := balancedEighteenTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
