/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A normalized six-output seed of weight 10, with degree 5/5 columns
and verified Hilbert tests at degrees 2 and 3. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem sixOutputTenSeedU_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputTenSeedU (R:=R) i).natDegree≤5 := by
  have hl : ∀i:Fin 6,(sixOutputTenSeedUData i).length≤6 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputTenSeedUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem sixOutputTenSeedV_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputTenSeedV (R:=R) i).natDegree≤5 := by
  have hl : ∀i:Fin 6,(sixOutputTenSeedVData i).length≤6 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputTenSeedVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sixOutputTenSeedSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputTenSeedWitness (R:=K)) 2 sixOutputTenSeedCoefficientRows).mulVec := by
  let e : (Fin 15 × Fin 3) ≃ Fin 45 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sixOutputTenSeedWitness (R:=K))
    2 sixOutputTenSeedCoefficientRows
  have he : M=(sixOutputTenSeedSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem sixOutputTenSeed_bounded_kernel_zero
    (v : Fin 15 → (ZMod 101)[X])
    (hv : sixOutputTenSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤2) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputTenSeedWitness 2 sixOutputTenSeedCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sixOutputTenSeed_selected_binding]
  exact sixOutputTenSeedSelected_injective

theorem sixOutputTenSeed_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputTenSeedWitness (R:=K)) 2 sixOutputTenSeedCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sixOutputTenSeed_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputTenSeed_selected_integer_binding, sixOutputTenSeed_selected_binding]
  exact sixOutputTenSeedSelected_injective

theorem sixOutputTenSeed_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 15 → K[X])
    (hv : sixOutputTenSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤2) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputTenSeedWitness 2 sixOutputTenSeedCoefficientRows
      sixOutputTenSeed_coefficient_injective_charZero v hv hdeg


theorem sixOutputTenSeedU_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputTenSeedU (R:=R) i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (sixOutputTenSeedUData j).getD 0 0=
      (![1,0,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (sixOutputTenSeedUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem sixOutputTenSeedV_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (sixOutputTenSeedV (R:=R) i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (sixOutputTenSeedVData j).getD 0 0=
      (![0,-1,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (sixOutputTenSeedVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num


theorem sixOutputTenSeedCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (sixOutputTenSeedCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [sixOutputTenSeedCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputTenSeedCritical_selected_integer_binding,
    sixOutputTenSeedCritical_selected_binding]
  exact sixOutputTenSeedCriticalSelected_injective

theorem sixOutputTenSeed_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    54 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputTenSeedWitness (R:=K)) 3
        sixOutputTenSeedCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (sixOutputTenSeedWitness (R:=K)) 3
    sixOutputTenSeedCriticalCoefficientRows
  let select : Fin 54 → Fin 15 × Fin 4 := fun j =>
    (finProdFinEquiv : Fin 15 × Fin 4 ≃ Fin 60).symm (sixOutputTenSeedCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    sixOutputTenSeedCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 54) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem sixOutputTenSeed_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (sixOutputTenSeedWitness (R:=K)) 3)≤6 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (sixOutputTenSeedWitness (R:=K)) 3 sixOutputTenSeedCriticalCoefficientRows
  have hr := sixOutputTenSeed_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
