/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CyclicPolynomialLeading
import FD56.LinearAlgebra.WeightedLeadingDivisors

/-! Tridiagonal weights give explicit monomial leading cyclic determinants. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K σ : Type*} [Field K] {n : ℕ}

def cyclicVariableMatrix (v : Fin (n+1) × Fin (n+1) → σ) :
    Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial σ K) :=
  fun i j => MvPolynomial.X (v (i,j))

def upperCyclicMonomial (v : Fin (n+1) × Fin (n+1) → σ) : MvPolynomial σ K :=
  ∏ k : Fin (n+1), ∏ i : Fin k.val,
    MvPolynomial.X (v (⟨i.val,by omega⟩,⟨i.val+1,by omega⟩))

theorem upperCyclicMonomial_ne_zero (v : Fin (n+1) × Fin (n+1) → σ) :
    upperCyclicMonomial (K := K) v ≠ 0 := by
  classical
  apply Finset.prod_ne_zero_iff.mpr
  intro k hk
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact MvPolynomial.X_ne_zero _

theorem weighted_cyclic_leading_coefficient (v : Fin (n+1) × Fin (n+1) → σ)
    (w : σ → ℕ)
    (hw : ∀ i j, w (v (i,j)) = if i.val+1=j.val ∨ j.val+1=i.val then 1 else 0) :
    (weightedVariableLift w (firstCyclicMatrix (cyclicVariableMatrix (K := K) v)).det).leadingCoeff =
      upperCyclicMonomial v := by
  classical
  let L := (cyclicVariableMatrix (K := K) v).map (weightedVariableLift w)
  let A : Matrix (Fin (n+1)) (Fin (n+1)) (MvPolynomial σ K) :=
    fun i j => if i.val+1=j.val ∨ j.val+1=i.val then MvPolynomial.X (v (i,j)) else 0
  have hL : ∀ i j, (L i j).natDegree ≤ 1 := by
    intro i j
    change (weightedVariableLift w (MvPolynomial.X (v (i,j)))).natDegree ≤ 1
    simp only [weightedVariableLift,MvPolynomial.eval₂Hom_X',hw]
    split_ifs <;> simp
  have hA : (Matrix.of fun i j => (L i j).coeff 1) = A := by
    funext i j
    change (weightedVariableLift w (MvPolynomial.X (v (i,j)))).coeff 1 = _
    simp only [weightedVariableLift,MvPolynomial.eval₂Hom_X',hw,A]
    split_ifs <;> simp
  have hAz : ∀ i j, i.val+1 < j.val → A i j = 0 := by
    intro i j hij
    simp [A,show ¬ (i.val+1=j.val ∨ j.val+1=i.val) by omega]
  have hdet : (firstCyclicMatrix A).det = upperCyclicMonomial v := by
    rw [firstCyclicMatrix_det_of_hessenberg A hAz]
    apply Finset.prod_congr rfl
    intro k hk
    apply Finset.prod_congr rfl
    intro i hi
    simp [A]
  have htop : (firstCyclicMatrix L).det.coeff (∑ i : Fin (n+1), i.val) =
      upperCyclicMonomial v := by
    rw [firstCyclicMatrix_polynomial_top_coefficient L hL,hA,hdet]
  have hdegree : (firstCyclicMatrix L).det.natDegree = ∑ i : Fin (n+1), i.val :=
    Polynomial.natDegree_eq_of_le_of_coeff_ne_zero
      (firstCyclicMatrix_polynomial_degree_le L hL)
      (by rw [htop]; exact upperCyclicMonomial_ne_zero v)
  rw [RingHom.map_det]
  change ((firstCyclicMatrix (cyclicVariableMatrix (K := K) v)).map
    (weightedVariableLift w)).det.leadingCoeff = _
  rw [firstCyclicMatrix_map]
  change (firstCyclicMatrix L).det.leadingCoeff = _
  rw [Polynomial.leadingCoeff,hdegree,htop]

end FD56
