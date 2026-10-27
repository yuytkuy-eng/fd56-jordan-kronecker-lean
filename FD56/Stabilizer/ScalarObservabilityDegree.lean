/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ScalarDiagonalObservability
import FD56.Stabilizer.StructuredLeading

/-! Exact weighted degree of the affine diagonal scalar-output witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {N : ℕ}

theorem scalarDiagonalState_degree (a : Fin N → K) :
    DegreeBound (scalarDiagonalState a) 1 := by
  intro i j
  by_cases h : i = j
  · subst j
    simp only [scalarDiagonalState, Matrix.diagonal_apply_eq]
    apply Polynomial.natDegree_add_le_of_degree_le
    · exact Polynomial.natDegree_mul_le.trans (by simp)
    · simp
  · simp [scalarDiagonalState, Matrix.diagonal_apply_ne _ h]

theorem scalarDiagonalOutput_degree (a : Fin N → K) :
    DegreeBound (scalarDiagonalOutput a) 1 := by
  intro i j
  exact Polynomial.natDegree_add_le_of_degree_le (by simp) (by simp)

theorem scalarDiagonalState_leading (a : Fin N → K) :
    matrixCoeff (scalarDiagonalState a) 1 = Matrix.diagonal a := by
  funext i j
  by_cases h : i = j
  · subst j
    simp only [matrixCoeff, scalarDiagonalState, Matrix.diagonal_apply_eq,
      coeff_add, coeff_C_mul, coeff_X_one, coeff_C, one_ne_zero, if_false, mul_one, add_zero]
  · simp [matrixCoeff, scalarDiagonalState, Matrix.diagonal_apply, h]

theorem scalarDiagonalOutput_leading (a : Fin N → K) :
    matrixCoeff (scalarDiagonalOutput a) 1 = fun _ _ => 1 := by
  funext i j
  simp [matrixCoeff, scalarDiagonalOutput]

theorem scalarDiagonalObservability_row_degree_top (a : Fin N → K) (i j : Fin N) :
    (scalarDiagonalObservability a i j).natDegree ≤ i.val + 1 ∧
      (scalarDiagonalObservability a i j).coeff (i.val + 1) = a j ^ i.val := by
  have h := observability_polynomial_degree_top (scalarDiagonalState a)
    (scalarDiagonalOutput a) N (scalarDiagonalState_degree a)
    (scalarDiagonalOutput_degree a) (i,0) j
  rw [scalarDiagonalState_leading, scalarDiagonalOutput_leading] at h
  simpa [scalarDiagonalObservability_eq_selected, observabilitySelectedMatrix,
    observabilityMatrix, Matrix.diagonal_pow, Matrix.mul_diagonal] using h

theorem scalarDiagonalObservability_natDegree (a : Fin N → K) (ha : Function.Injective a) :
    (scalarDiagonalObservability a).det.natDegree = ∑ i : Fin N, (i.val + 1) := by
  apply polynomial_det_natDegree_eq_row_sum _ _
    (fun i j => (scalarDiagonalObservability_row_degree_top a i j).1)
  have he : (fun i j => (scalarDiagonalObservability a i j).coeff (i.val + 1)) =
      (Matrix.vandermonde a).transpose := by
    funext i j
    exact (scalarDiagonalObservability_row_degree_top a i j).2
  rw [he, Matrix.det_transpose]
  exact Matrix.det_vandermonde_ne_zero_iff.mpr ha

end FD56
