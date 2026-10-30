/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PermutedSixOutputThreeTailBinding

/-! A degree-three tail with permuted endpoints with a verified degree-one kernel test. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 1600000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

theorem permutedSixOutputThreeTailU_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailU (R:=R) i).natDegree≤3 := by
  have hl : ∀i:Fin 6,(permutedSixOutputThreeTailUData i).length≤4 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (permutedSixOutputThreeTailUData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

theorem permutedSixOutputThreeTailV_degree {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailV (R:=R) i).natDegree≤3 := by
  have hl : ∀i:Fin 6,(permutedSixOutputThreeTailVData i).length≤4 := by decide +kernel
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (permutedSixOutputThreeTailVData i) : R[X]).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hl i; omega)]
  simp

private theorem coefficient_injective {K : Type*} [Field K]
    (hinj : Function.Injective (permutedSixOutputThreeTailSelectedCoefficient (K:=K)).mulVec) :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (permutedSixOutputThreeTailWitness (R:=K)) 1 permutedSixOutputThreeTailCoefficientRows).mulVec := by
  let e : (Fin 15 × Fin 2) ≃ Fin 30 := finProdFinEquiv
  let M := selectedPolynomialCoefficientMatrix (permutedSixOutputThreeTailWitness (R:=K))
    1 permutedSixOutputThreeTailCoefficientRows
  have he : M=(permutedSixOutputThreeTailSelectedCoefficient (K:=K)).submatrix id e := by
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

theorem permutedSixOutputThreeTail_bounded_kernel_zero
    (v : Fin 15 → (ZMod 101)[X])
    (hv : permutedSixOutputThreeTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤1) : v=0 := by
  apply bounded_kernel_zero_of_selected_coefficient_injective
    permutedSixOutputThreeTailWitness 1 permutedSixOutputThreeTailCoefficientRows _ v hv hdeg
  apply coefficient_injective
  rw [permutedSixOutputThreeTail_selected_binding]
  exact permutedSixOutputThreeTailSelected_injective

theorem permutedSixOutputThreeTail_coefficient_injective_charZero
    {K : Type*} [Field K] [CharZero K] :
    Function.Injective (selectedPolynomialCoefficientMatrix
      (permutedSixOutputThreeTailWitness (R:=K)) 1 permutedSixOutputThreeTailCoefficientRows).mulVec := by
  apply coefficient_injective
  rw [permutedSixOutputThreeTail_selected_integer_binding]
  apply matrix_injective_of_field_specialization (Int.castRingHom (ZMod 101))
    (Int.castRingHom K) Int.cast_injective
  rw [← permutedSixOutputThreeTail_selected_integer_binding, permutedSixOutputThreeTail_selected_binding]
  exact permutedSixOutputThreeTailSelected_injective

theorem permutedSixOutputThreeTail_bounded_kernel_zero_charZero
    {K : Type*} [Field K] [CharZero K]
    (v : Fin 15 → K[X])
    (hv : permutedSixOutputThreeTailWitness *ᵥ v=0) (hdeg : ∀j,(v j).natDegree≤1) : v=0 :=
  bounded_kernel_zero_of_selected_coefficient_injective
    permutedSixOutputThreeTailWitness 1 permutedSixOutputThreeTailCoefficientRows
      permutedSixOutputThreeTail_coefficient_injective_charZero v hv hdeg


theorem permutedSixOutputThreeTailU_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailU (R:=R) i).coeff 0=(![0,0,1,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (permutedSixOutputThreeTailUData j).getD 0 0=
      (![0,0,1,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (permutedSixOutputThreeTailUData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem permutedSixOutputThreeTailU_top {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailU (R:=R) i).coeff 3=(![1,0,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (permutedSixOutputThreeTailUData j).getD 3 0=
      (![1,0,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (permutedSixOutputThreeTailUData i) : R[X]).coeff 3=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem permutedSixOutputThreeTailV_constant {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailV (R:=R) i).coeff 0=(![0,0,0,-1,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (permutedSixOutputThreeTailVData j).getD 0 0=
      (![0,0,0,-1,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (permutedSixOutputThreeTailVData i) : R[X]).coeff 0=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

theorem permutedSixOutputThreeTailV_top {R : Type*} [CommRing R] (i : Fin 6) :
    (permutedSixOutputThreeTailV (R:=R) i).coeff 3=(![0,-1,0,0,0,0] : Fin 6 → R) i := by
  have hdata : ∀ j : Fin 6, (permutedSixOutputThreeTailVData j).getD 3 0=
      (![0,-1,0,0,0,0] : Fin 6 → ℤ) j := by decide +kernel
  change (integerPolynomial (permutedSixOutputThreeTailVData i) : R[X]).coeff 3=_
  rw [integerPolynomial_coeff,hdata]
  fin_cases i <;> norm_num

end FD56
