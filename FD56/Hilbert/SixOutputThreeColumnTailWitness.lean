/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailBinding

/-! A concrete degree-five three-column frame with no tangent kernel through degree five. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem sixOutputThreeColumnTailFrame_degree {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnTailFrame (R:=R) i j).natDegree≤5 := by
  have hl : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnTailFrameData i j).length≤6 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (sixOutputThreeColumnTailFrameData i j) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i j; omega)]
  simp

theorem sixOutputThreeColumnTailFrame_constant {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnTailFrame (R:=R) i j).coeff 0=(if i.val=j.val then 1 else 0 : R) := by
  have hdata : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnTailFrameData i j).getD 0 0=
      (if i.val=j.val then 1 else 0 : ℤ) := by decide +kernel
  change (integerPolynomial (sixOutputThreeColumnTailFrameData i j) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  split_ifs <;> simp

theorem sixOutputThreeColumnTailFrame_top {R : Type*} [CommRing R] (i : Fin 6) (j : Fin 3) :
    (sixOutputThreeColumnTailFrame (R:=R) i j).coeff 5=(if i.val=j.val+3 then 1 else 0 : R) := by
  have hdata : ∀ i : Fin 6, ∀ j : Fin 3, (sixOutputThreeColumnTailFrameData i j).getD 5 0=
      (if i.val=j.val+3 then 1 else 0 : ℤ) := by decide +kernel
  change (integerPolynomial (sixOutputThreeColumnTailFrameData i j) : R[X]).coeff 5=_
  rw [integerPolynomial_coeff,hdata]
  split_ifs <;> simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (sixOutputThreeColumnTailSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnTailWitness (R:=K)) 5 sixOutputThreeColumnTailCoefficientRows).mulVec := by
  let e : (Fin 20 × Fin 6) ≃ Fin 120 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (sixOutputThreeColumnTailWitness (R:=K))
    5 sixOutputThreeColumnTailCoefficientRows
  have he : M=(sixOutputThreeColumnTailSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem sixOutputThreeColumnTail_bounded_kernel_zero
    (v : Fin 20 → (ZMod 101)[X])
    (hv : sixOutputThreeColumnTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnTailWitness 5 sixOutputThreeColumnTailCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [sixOutputThreeColumnTail_selected_binding]
  exact sixOutputThreeColumnTailSelected_injective

theorem sixOutputThreeColumnTail_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (sixOutputThreeColumnTailWitness (R:=K)) 5 sixOutputThreeColumnTailCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [sixOutputThreeColumnTail_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← sixOutputThreeColumnTail_selected_integer_binding, sixOutputThreeColumnTail_selected_binding]
  exact sixOutputThreeColumnTailSelected_injective

theorem sixOutputThreeColumnTail_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 20 → K[X])
    (hv : sixOutputThreeColumnTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤5) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    sixOutputThreeColumnTailWitness 5 sixOutputThreeColumnTailCoefficientRows
      sixOutputThreeColumnTail_coefficient_injective_charZero v hv hdeg


end FD56
