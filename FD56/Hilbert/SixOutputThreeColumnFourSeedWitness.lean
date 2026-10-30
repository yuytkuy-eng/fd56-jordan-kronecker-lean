/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedBinding
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A degree-four three-column seed with exact Hilbert tests at degrees three and four. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem sixOutputThreeColumnFourSeedFrame_degree {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnFourSeedFrame (R:=R) i j).natDegree≤4 := by
  have hl : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnFourSeedFrameData i j).length≤5 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputThreeColumnFourSeedFrameData i j) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i j; omega)]
  simp

theorem sixOutputThreeColumnFourSeedFrame_constant {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnFourSeedFrame (R:=R) i j).coeff 0=(if i.val=j.val+3 then 1 else 0 : R) := by
  have hdata : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnFourSeedFrameData i j).getD 0 0=
      (if i.val=j.val+3 then 1 else 0 : ℤ) := by decide +kernel
  change (integerPolynomial (sixOutputThreeColumnFourSeedFrameData i j) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  split_ifs <;> simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sixOutputThreeColumnFourSeedSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnFourSeedWitness (R:=K)) 3 sixOutputThreeColumnFourSeedCoefficientRows).mulVec := by
  let e : (Fin 20 × Fin 4) ≃ Fin 80 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sixOutputThreeColumnFourSeedWitness (R:=K))
    3 sixOutputThreeColumnFourSeedCoefficientRows
  have he : M=(sixOutputThreeColumnFourSeedSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem sixOutputThreeColumnFourSeed_bounded_kernel_zero
    (v : Fin 20 → (ZMod 101)[X])
    (hv : sixOutputThreeColumnFourSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnFourSeedWitness 3 sixOutputThreeColumnFourSeedCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sixOutputThreeColumnFourSeed_selected_binding]
  exact sixOutputThreeColumnFourSeedSelected_injective

theorem sixOutputThreeColumnFourSeed_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnFourSeedWitness (R:=K)) 3 sixOutputThreeColumnFourSeedCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sixOutputThreeColumnFourSeed_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputThreeColumnFourSeed_selected_integer_binding, sixOutputThreeColumnFourSeed_selected_binding]
  exact sixOutputThreeColumnFourSeedSelected_injective

theorem sixOutputThreeColumnFourSeed_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 20 → K[X])
    (hv : sixOutputThreeColumnFourSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnFourSeedWitness 3 sixOutputThreeColumnFourSeedCoefficientRows
      sixOutputThreeColumnFourSeed_coefficient_injective_charZero v hv hdeg


theorem sixOutputThreeColumnFourSeedCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (sixOutputThreeColumnFourSeedCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [sixOutputThreeColumnFourSeedCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputThreeColumnFourSeedCritical_selected_integer_binding,
    sixOutputThreeColumnFourSeedCritical_selected_binding]
  exact sixOutputThreeColumnFourSeedCriticalSelected_injective

theorem sixOutputThreeColumnFourSeed_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    98 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnFourSeedWitness (R:=K)) 4
        sixOutputThreeColumnFourSeedCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (sixOutputThreeColumnFourSeedWitness (R:=K)) 4
    sixOutputThreeColumnFourSeedCriticalCoefficientRows
  let select : Fin 98 → Fin 20 × Fin 5 := fun j =>
    (finProdFinEquiv : Fin 20 × Fin 5 ≃ Fin 100).symm (sixOutputThreeColumnFourSeedCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    sixOutputThreeColumnFourSeedCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 98) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem sixOutputThreeColumnFourSeed_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (sixOutputThreeColumnFourSeedWitness (R:=K)) 4)≤2 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (sixOutputThreeColumnFourSeedWitness (R:=K)) 4 sixOutputThreeColumnFourSeedCriticalCoefficientRows
  have hr := sixOutputThreeColumnFourSeed_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
