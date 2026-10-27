/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.IndependentSubsetSums
import FD56.LinearAlgebra.WeightedDeterminantDegree
import FD56.Stabilizer.ObservabilityScalarAdjugate
import Mathlib.LinearAlgebra.Vandermonde

/-! An affine diagonal observability witness with distinct explicitly described poles. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {N : ℕ}

def scalarDiagonalState (a : Fin N → R) : Matrix (Fin N) (Fin N) R[X] :=
  Matrix.diagonal (fun j => C (a j) * X + C (a j ^ 2))

def scalarDiagonalOutput (a : Fin N → R) : Matrix (Fin 1) (Fin N) R[X] :=
  fun _ j => X + C (a j)

def scalarDiagonalObservability (a : Fin N → R) : Matrix (Fin N) (Fin N) R[X] :=
  fun i j => (X + C (a j)) * (C (a j) * X + C (a j ^ 2)) ^ i.val

def scalarObservabilityPoleValue (a : Fin N → R) (s : scalarObservabilityPoleIndex N) : R :=
  -(∑ i ∈ scalarObservabilityPoleSupport s, a i)

theorem scalarDiagonalObservability_eq_selected (a : Fin N → R) :
    scalarDiagonalObservability a = observabilitySelectedMatrix
      (scalarDiagonalState a) (scalarDiagonalOutput a) Fin.val (fun _ => 0) := by
  ext i j
  simp [scalarDiagonalObservability, observabilitySelectedMatrix, scalarDiagonalState,
    scalarDiagonalOutput, Matrix.diagonal_pow, Matrix.mul_diagonal]

theorem scalarDiagonalObservability_det (a : Fin N → R) :
    (scalarDiagonalObservability a).det =
      (∏ i, (X + C (a i))) *
      ∏ i : Fin N, ∏ j ∈ Finset.Ioi i,
        ((C (a j) * X + C (a j ^ 2)) - (C (a i) * X + C (a i ^ 2))) := by
  have he : scalarDiagonalObservability a =
      (Matrix.vandermonde (fun j => C (a j) * X + C (a j ^ 2))).transpose *
        Matrix.diagonal (fun j => X + C (a j)) := by
    funext i j
    simp only [scalarDiagonalObservability, Matrix.mul_diagonal, Matrix.transpose_apply,
      Matrix.vandermonde_apply]
    exact mul_comm _ _
  rw [he, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal, Matrix.det_vandermonde]
  exact mul_comm _ _

theorem scalarObservabilityPole_product (a : Fin N → R) :
    (∏ s : scalarObservabilityPoleIndex N, (X - C (scalarObservabilityPoleValue a s))) =
      (∏ i, (X + C (a i))) *
        ∏ i : Fin N, ∏ j ∈ Finset.Ioi i, (X + C (a i + a j)) := by
  change (∏ s : Fin N ⊕ (Σ i : Fin N, {j : Fin N // i < j}), _) = _
  rw [Fintype.prod_sum_type, Fintype.prod_sigma]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [scalarObservabilityPoleValue, scalarObservabilityPoleSupport]
  · apply Finset.prod_congr rfl
    intro i _
    rw [Finset.prod_subtype (p := fun j : Fin N => i < j) (Finset.Ioi i) (by simp)]
    apply Finset.prod_congr rfl
    intro j _
    simp [scalarObservabilityPoleValue, scalarObservabilityPoleSupport, ne_of_lt j.property]
    ring

theorem scalarDiagonalObservability_factorization (a : Fin N → R) :
    (scalarDiagonalObservability a).det =
      C (Matrix.vandermonde a).det *
        ∏ s : scalarObservabilityPoleIndex N, (X - C (scalarObservabilityPoleValue a s)) := by
  rw [scalarDiagonalObservability_det, scalarObservabilityPole_product, Matrix.det_vandermonde]
  have hf (i j : Fin N) :
      C (a j) * X + C (a j ^ 2) - (C (a i) * X + C (a i ^ 2)) =
        C (a j - a i) * (X + C (a i + a j)) := by
    simp only [map_sub, map_add, map_pow]
    ring
  simp_rw [hf, Finset.prod_mul_distrib]
  simp only [map_prod]
  ring

theorem scalarDiagonalObservability_separable {K F : Type*} [Field K] [Field F]
    (N : ℕ) (ι : MvPolynomial (Fin N) K →+* F) (hι : Function.Injective ι) :
    (scalarDiagonalObservability (fun i => ι (MvPolynomial.X i))).det.Separable := by
  rw [scalarDiagonalObservability_factorization]
  apply Polynomial.Separable.unit_mul
  · apply isUnit_C.mpr
    apply isUnit_iff_ne_zero.mpr
    exact Matrix.det_vandermonde_ne_zero_iff.mpr (hι.comp MvPolynomial.X_injective)
  · apply Polynomial.separable_prod_X_sub_C_iff.mpr
    exact independent_scalar_observability_poles_injective N ι hι

end FD56
