/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSeventeenTangentCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized total-weight17 seed with degree8/9 columns and
verified bounded-kernel tests at degrees3 and4. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem balancedSeventeenTangentU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentU (R:=R) i).natDegree≤8 := by
  have hl : ∀i:Fin 5,(balancedSeventeenTangentUData i).length≤9 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedSeventeenTangentUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem balancedSeventeenTangentV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentV (R:=R) i).natDegree≤9 := by
  have hl : ∀i:Fin 5,(balancedSeventeenTangentVData i).length≤10 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (balancedSeventeenTangentVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (balancedSeventeenTangentSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedSeventeenTangentWitness (R:=K)) 3 balancedSeventeenTangentCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 4) ≃ Fin 40 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (balancedSeventeenTangentWitness (R:=K))
    3 balancedSeventeenTangentCoefficientRows
  have he : M=(balancedSeventeenTangentSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem balancedSeventeenTangent_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : balancedSeventeenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    balancedSeventeenTangentWitness 3 balancedSeventeenTangentCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [balancedSeventeenTangent_selected_binding]
  exact balancedSeventeenTangentSelected_injective

theorem balancedSeventeenTangent_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (balancedSeventeenTangentWitness (R:=K)) 3 balancedSeventeenTangentCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [balancedSeventeenTangent_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedSeventeenTangent_selected_integer_binding, balancedSeventeenTangent_selected_binding]
  exact balancedSeventeenTangentSelected_injective

theorem balancedSeventeenTangent_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : balancedSeventeenTangentWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    balancedSeventeenTangentWitness 3 balancedSeventeenTangentCoefficientRows
      balancedSeventeenTangent_coefficient_injective_charZero v hv hdeg


theorem balancedSeventeenTangentU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSeventeenTangentUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSeventeenTangentUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSeventeenTangentU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentU (R:=R) i).coeff 8=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSeventeenTangentUData j).getD 8 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSeventeenTangentUData i) : R[X]).coeff 8=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSeventeenTangentV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSeventeenTangentVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSeventeenTangentVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSeventeenTangentV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (balancedSeventeenTangentV (R:=R) i).coeff 9=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (balancedSeventeenTangentVData j).getD 9 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (balancedSeventeenTangentVData i) : R[X]).coeff 9=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem balancedSeventeenTangentCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (balancedSeventeenTangentCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [balancedSeventeenTangentCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← balancedSeventeenTangentCritical_selected_integer_binding,
    balancedSeventeenTangentCritical_selected_binding]
  exact balancedSeventeenTangentCriticalSelected_injective

theorem balancedSeventeenTangent_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    49 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (balancedSeventeenTangentWitness (R:=K)) 4
        balancedSeventeenTangentCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (balancedSeventeenTangentWitness (R:=K)) 4
    balancedSeventeenTangentCriticalCoefficientRows
  let select : Fin 49 → Fin 10 × Fin 5 := fun j =>
    (finProdFinEquiv : Fin 10 × Fin 5 ≃ Fin 50).symm (balancedSeventeenTangentCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    balancedSeventeenTangentCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 49) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem balancedSeventeenTangent_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (balancedSeventeenTangentWitness (R:=K)) 4)≤1 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (balancedSeventeenTangentWitness (R:=K)) 4 balancedSeventeenTangentCriticalCoefficientRows
  have hr := balancedSeventeenTangent_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
