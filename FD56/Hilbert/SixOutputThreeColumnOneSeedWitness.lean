/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedCriticalBinding
import FD56.Hilbert.SelectedCoefficientDimension

/-! A concrete degree-one three-column frame with no tangent kernel through degree zero. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem sixOutputThreeColumnOneSeedFrame_degree {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnOneSeedFrame (R:=R) i j).natDegree≤1 := by
  have hl : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnOneSeedFrameData i j).length≤2 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputThreeColumnOneSeedFrameData i j) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i j; omega)]
  simp

theorem sixOutputThreeColumnOneSeedFrame_constant {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnOneSeedFrame (R:=R) i j).coeff 0=(if i.val=j.val+3 then 1 else 0 : R) := by
  have hdata : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnOneSeedFrameData i j).getD 0 0=
      (if i.val=j.val+3 then 1 else 0 : ℤ) := by decide +kernel
  change (integerPolynomial (sixOutputThreeColumnOneSeedFrameData i j) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  split_ifs <;> simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sixOutputThreeColumnOneSeedSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnOneSeedWitness (R:=K)) 0 sixOutputThreeColumnOneSeedCoefficientRows).mulVec := by
  let e : (Fin 20 × Fin 1) ≃ Fin 20 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sixOutputThreeColumnOneSeedWitness (R:=K))
    0 sixOutputThreeColumnOneSeedCoefficientRows
  have he : M=(sixOutputThreeColumnOneSeedSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem sixOutputThreeColumnOneSeed_bounded_kernel_zero
    (v : Fin 20 → (ZMod 101)[X])
    (hv : sixOutputThreeColumnOneSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤0) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnOneSeedWitness 0 sixOutputThreeColumnOneSeedCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sixOutputThreeColumnOneSeed_selected_binding]
  exact sixOutputThreeColumnOneSeedSelected_injective

theorem sixOutputThreeColumnOneSeed_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnOneSeedWitness (R:=K)) 0 sixOutputThreeColumnOneSeedCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sixOutputThreeColumnOneSeed_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputThreeColumnOneSeed_selected_integer_binding, sixOutputThreeColumnOneSeed_selected_binding]
  exact sixOutputThreeColumnOneSeedSelected_injective

theorem sixOutputThreeColumnOneSeed_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 20 → K[X])
    (hv : sixOutputThreeColumnOneSeedWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤0) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnOneSeedWitness 0 sixOutputThreeColumnOneSeedCoefficientRows
      sixOutputThreeColumnOneSeed_coefficient_injective_charZero v hv hdeg


theorem sixOutputThreeColumnOneSeedCritical_selected_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (sixOutputThreeColumnOneSeedCriticalSelectedCoefficient (K:=K)).mulVec := by
  rw [sixOutputThreeColumnOneSeedCritical_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputThreeColumnOneSeedCritical_selected_integer_binding,
    sixOutputThreeColumnOneSeedCritical_selected_binding]
  exact sixOutputThreeColumnOneSeedCriticalSelected_injective

theorem sixOutputThreeColumnOneSeed_critical_coefficient_rank
    {K : Type*} [Field K] [CharZero K] :
    32 ≤ Module.finrank K (LinearMap.range (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix (sixOutputThreeColumnOneSeedWitness (R:=K)) 1
        sixOutputThreeColumnOneSeedCriticalCoefficientRows))) := by
  let A := selectedPolynomialCoefficientMatrix (sixOutputThreeColumnOneSeedWitness (R:=K)) 1
    sixOutputThreeColumnOneSeedCriticalCoefficientRows
  let select : Fin 32 → Fin 20 × Fin 2 := fun j =>
    (finProdFinEquiv : Fin 20 × Fin 2 ≃ Fin 40).symm (sixOutputThreeColumnOneSeedCriticalCoefficientColumns j)
  have hinj : Function.Injective (A.submatrix id select).mulVec :=
    sixOutputThreeColumnOneSeedCritical_selected_injective_charZero
  have hi := Matrix.mulVec_injective_iff.mp hinj
  change Fintype.card (Fin 32) ≤ Module.finrank K (LinearMap.range (Matrix.toLin' A))
  rw [Matrix.range_toLin',← finrank_span_eq_card hi]
  apply Submodule.finrank_mono
  apply Submodule.span_mono
  rintro _ ⟨j,rfl⟩
  exact ⟨select j,rfl⟩

theorem sixOutputThreeColumnOneSeed_kernel_finrank_critical_le
    {K : Type*} [Field K] [CharZero K] :
    Module.finrank K (polynomialKernelAtDegree (sixOutputThreeColumnOneSeedWitness (R:=K)) 1)≤8 := by
  have h := polynomial_kernel_finrank_add_selected_coefficient_rank_le
    (sixOutputThreeColumnOneSeedWitness (R:=K)) 1 sixOutputThreeColumnOneSeedCriticalCoefficientRows
  have hr := sixOutputThreeColumnOneSeed_critical_coefficient_rank (K:=K)
  simp only [Fintype.card_fin] at h
  omega

end FD56
