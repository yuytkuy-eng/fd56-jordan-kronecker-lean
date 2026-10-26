/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericCyclicLeading
import FD56.LinearAlgebra.DisjointMonomialDivisors

/-! The first and reversed last cyclic determinants of a universal matrix are coprime. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] (n : ℕ)

def cyclicAdjacentWeight (ij : Fin (n+1) × Fin (n+1)) : ℕ :=
  if ij.1.val+1=ij.2.val ∨ ij.2.val+1=ij.1.val then 1 else 0

def reverseMatrixVariable (ij : Fin (n+1) × Fin (n+1)) :
    Fin (n+1) × Fin (n+1) := (ij.1.rev,ij.2.rev)

theorem cyclicAdjacentWeight_reverse (i j : Fin (n+1)) :
    cyclicAdjacentWeight n (reverseMatrixVariable n (i,j)) =
      if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0 := by
  unfold cyclicAdjacentWeight reverseMatrixVariable
  simp only [Fin.val_rev]
  split_ifs <;> omega

theorem upper_reverse_cyclic_monomial_common_divisor_isUnit
    (p : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hfirst : p ∣ upperCyclicMonomial id)
    (hlast : p ∣ upperCyclicMonomial (reverseMatrixVariable n)) : IsUnit p := by
  classical
  let a : (Σ k : Fin (n+1), Fin k.val) → Fin (n+1) × Fin (n+1) :=
    fun ki => (⟨ki.2.val,by omega⟩,⟨ki.2.val+1,by omega⟩)
  have ha : upperCyclicMonomial (K := K) id = ∏ i, MvPolynomial.X (a i) := by
    rw [Fintype.prod_sigma]
    rfl
  have hb : upperCyclicMonomial (K := K) (reverseMatrixVariable n) =
      ∏ i, MvPolynomial.X (reverseMatrixVariable n (a i)) := by
    rw [Fintype.prod_sigma]
    rfl
  apply disjoint_variable_products_common_divisor_isUnit a
    (fun i => reverseMatrixVariable n (a i)) ?_ p (ha ▸ hfirst) (hb ▸ hlast)
  intro i j hij
  have h₁ := congrArg (fun z : Fin (n+1) × Fin (n+1) => z.1.val) hij
  have h₂ := congrArg (fun z : Fin (n+1) × Fin (n+1) => z.2.val) hij
  simp only [a,reverseMatrixVariable,Fin.val_rev] at h₁ h₂
  omega

theorem generic_cyclic_common_divisor_isUnit
    (p : MvPolynomial (Fin (n+1) × Fin (n+1)) K)
    (hfirst : p ∣ (firstCyclicMatrix (cyclicVariableMatrix id)).det)
    (hlast : p ∣ (firstCyclicMatrix (cyclicVariableMatrix (reverseMatrixVariable n))).det) :
    IsUnit p := by
  apply weighted_leading_common_divisor_isUnit (cyclicAdjacentWeight n) _ _ p ?_ hfirst hlast
  intro a ha hb
  rw [weighted_cyclic_leading_coefficient id (cyclicAdjacentWeight n) (by intro i j; rfl)] at ha
  rw [weighted_cyclic_leading_coefficient (reverseMatrixVariable n)
    (cyclicAdjacentWeight n) (cyclicAdjacentWeight_reverse n)] at hb
  exact upper_reverse_cyclic_monomial_common_divisor_isUnit n a ha hb

end FD56
