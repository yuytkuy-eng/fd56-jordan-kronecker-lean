/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized six-output seed of weight 8, with degree 4/4 columns
and verified Hilbert tests at degrees 1 and 2. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem sixOutputEightSeedU_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputEightSeedU (R:=R) i).natDegree≤4 := by
  have hl : ∀i:Fin 6,(sixOutputEightSeedUData i).length≤5 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputEightSeedUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem sixOutputEightSeedV_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputEightSeedV (R:=R) i).natDegree≤4 := by
  have hl : ∀i:Fin 6,(sixOutputEightSeedVData i).length≤5 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputEightSeedVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sixOutputEightSeedSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputEightSeedWitness (R:=K)) 1 sixOutputEightSeedCoefficientRows).mulVec := by
  let e : (Fin 15 × Fin 2) ≃ Fin 30 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sixOutputEightSeedWitness (R:=K))
    1 sixOutputEightSeedCoefficientRows
  have he : M=(sixOutputEightSeedSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem sixOutputEightSeed_bounded_kernel_zero
    (v : Fin 15 → (ZMod 101)[X])
    (hv : sixOutputEightSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤1) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputEightSeedWitness 1 sixOutputEightSeedCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sixOutputEightSeed_selected_binding]
  exact sixOutputEightSeedSelected_injective

theorem sixOutputEightSeed_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputEightSeedWitness (R:=K)) 1 sixOutputEightSeedCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sixOutputEightSeed_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputEightSeed_selected_integer_binding, sixOutputEightSeed_selected_binding]
  exact sixOutputEightSeedSelected_injective

theorem sixOutputEightSeed_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 15 → K[X])
    (hv : sixOutputEightSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤1) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputEightSeedWitness 1 sixOutputEightSeedCoefficientRows
      sixOutputEightSeed_coefficient_injective_charZero v hv hdeg


theorem sixOutputEightSeedU_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputEightSeedU (R:=R) i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (sixOutputEightSeedUData j).getD 0 0=
      (![1,0,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (sixOutputEightSeedUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem sixOutputEightSeedV_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputEightSeedV (R:=R) i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (sixOutputEightSeedVData j).getD 0 0=
      (![0,-1,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (sixOutputEightSeedVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num


theorem sixOutputEightSeedCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (sixOutputEightSeedCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [sixOutputEightSeedCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputEightSeedCritical_selected_integer_binding,
    sixOutputEightSeedCritical_selected_binding]
  exact sixOutputEightSeedCriticalSelected_injective

theorem sixOutputEightSeed_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    42 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputEightSeedWitness (R:=K)) 2
        sixOutputEightSeedCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (sixOutputEightSeedWitness (R:=K)) 2
    sixOutputEightSeedCriticalCoefficientRows
  let select : Fin 42 → Fin 15 × Fin 3 := fun j =>
    (finProdFinEquiv : Fin 15 × Fin 3 ≃ Fin 45).symm (sixOutputEightSeedCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    sixOutputEightSeedCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 42) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem sixOutputEightSeed_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (sixOutputEightSeedWitness (R:=K)) 2)≤3 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (sixOutputEightSeedWitness (R:=K)) 2 sixOutputEightSeedCriticalCoefficientRows
  have hr := sixOutputEightSeed_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
