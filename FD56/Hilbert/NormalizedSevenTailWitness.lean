/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSevenTailBinding

/-! A normalized degree-seven tail with a verified degree-three kernel test. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem normalizedSevenTailU_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailU (R:=R) i).natDegree≤7 := by
  have hl : ∀i:Fin 5,(normalizedSevenTailUData i).length≤8 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (normalizedSevenTailUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem normalizedSevenTailV_degree {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailV (R:=R) i).natDegree≤7 := by
  have hl : ∀i:Fin 5,(normalizedSevenTailVData i).length≤8 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (normalizedSevenTailVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (normalizedSevenTailSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (normalizedSevenTailWitness (R:=K)) 3 normalizedSevenTailCoefficientRows).mulVec := by
  let e : (Fin 10 × Fin 4) ≃ Fin 40 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (normalizedSevenTailWitness (R:=K))
    3 normalizedSevenTailCoefficientRows
  have he : M=(normalizedSevenTailSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem normalizedSevenTail_bounded_kernel_zero
    (v : Fin 10 → (ZMod 101)[X])
    (hv : normalizedSevenTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    normalizedSevenTailWitness 3 normalizedSevenTailCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [normalizedSevenTail_selected_binding]
  exact normalizedSevenTailSelected_injective

theorem normalizedSevenTail_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (normalizedSevenTailWitness (R:=K)) 3 normalizedSevenTailCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [normalizedSevenTail_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← normalizedSevenTail_selected_integer_binding, normalizedSevenTail_selected_binding]
  exact normalizedSevenTailSelected_injective

theorem normalizedSevenTail_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 10 → K[X])
    (hv : normalizedSevenTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤3) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    normalizedSevenTailWitness 3 normalizedSevenTailCoefficientRows
      normalizedSevenTail_coefficient_injective_charZero v hv hdeg


theorem normalizedSevenTailU_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailU (R:=R) i).coeff 0=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (normalizedSevenTailUData j).getD 0 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (normalizedSevenTailUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem normalizedSevenTailU_top {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailU (R:=R) i).coeff 7=(![1,0,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (normalizedSevenTailUData j).getD 7 0=
      (![1,0,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (normalizedSevenTailUData i) : R[X]).coeff 7=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem normalizedSevenTailV_constant {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailV (R:=R) i).coeff 0=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (normalizedSevenTailVData j).getD 0 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (normalizedSevenTailVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem normalizedSevenTailV_top {R : Type*} [CommRing R] (i : Fin 5) :
    (normalizedSevenTailV (R:=R) i).coeff 7=(![0,-1,0,0,0] : Fin 5 → R) i := by
  have hdata : ∀ j : Fin 5, (normalizedSevenTailVData j).getD 7 0=
      (![0,-1,0,0,0] : Fin 5 → ℤ) j := by decide +kernel
  change (integerPolynomial (normalizedSevenTailVData i) : R[X]).coeff 7=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

end FD56
