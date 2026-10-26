/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SingletonGenerator
import FD56.LinearAlgebra.RectangularMinorDivisors
import FD56.LinearAlgebra.WeightedDeterminantDegree
import FD56.LinearAlgebra.NonzeroMaximalMinor

/-! Primitive corank-one polynomial matrices have the row-sum kernel degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {N : ℕ}

theorem right_rectangularCofactor_eq (A : Matrix (Fin N) (Fin (N+1)) K[X]) (j : Fin (N+1)) :
    rectangularCofactors A.transpose j =
      Polynomial.C ((-1 : K)^j.val) * (A.submatrix id j.succAbove).det := by
  simp only [rectangularCofactors,map_pow,map_neg,map_one]
  congr 1
  exact Matrix.det_transpose _

theorem right_rectangularCofactor_degree (A : Matrix (Fin N) (Fin (N+1)) K[X])
    (e : Fin N → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ e i) (j : Fin (N+1)) :
    (rectangularCofactors A.transpose j).natDegree ≤ ∑ i, e i := by
  rw [right_rectangularCofactor_eq]
  exact (Polynomial.natDegree_C_mul_le _ _).trans
    (polynomial_det_natDegree_le_row_sum (A.submatrix id j.succAbove) e (fun i k => hA i _))

theorem right_rectangularCofactor_top_coefficient (A : Matrix (Fin N) (Fin (N+1)) K[X])
    (e : Fin N → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ e i) (j : Fin (N+1)) :
    (rectangularCofactors A.transpose j).coeff (∑ i, e i) =
      (-1 : K)^j.val * ((Matrix.of fun i k => (A i k).coeff (e i)).submatrix id j.succAbove).det := by
  rw [right_rectangularCofactor_eq,Polynomial.coeff_C_mul,
    polynomial_det_coefficient_row_sum (A.submatrix id j.succAbove) e (fun i k => hA i _)]
  rfl

theorem right_rectangularCofactors_nonzero_top (A : Matrix (Fin N) (Fin (N+1)) K[X])
    (e : Fin N → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hL : Function.Injective (Matrix.mulVec
      ((Matrix.of fun i k => (A i k).coeff (e i)).transpose))) :
    ∃ j, (rectangularCofactors A.transpose j).coeff (∑ i, e i) ≠ 0 := by
  classical
  let L : Matrix (Fin N) (Fin (N+1)) K := fun i k => (A i k).coeff (e i)
  obtain ⟨r,hr⟩ := exists_nonzero_maximal_minor_of_injective L.transpose hL
  by_contra hn
  have hz : ∀ j, (rectangularCofactors A.transpose j).coeff (∑ i, e i) = 0 := by simpa using hn
  have hm : ∀ j : Fin (N+1), (L.transpose.submatrix j.succAbove id).det = 0 := by
    intro j
    have hh := hz j
    rw [right_rectangularCofactor_top_coefficient A e hA j] at hh
    have he : (L.submatrix id j.succAbove).det = 0 :=
      (mul_eq_zero.mp hh).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
    change (L.submatrix id j.succAbove).transpose.det = 0
    rwa [Matrix.det_transpose]
  have hd := rectangular_maximal_minors_dvd_of_row_minors L.transpose 0
    (fun j => by rw [hm j]) r
  exact hr (zero_dvd_iff.mp hd)

theorem corank_one_finite_minimal_degree (A : Matrix (Fin N) (Fin (N+1)) K[X])
    (e : Fin N → ℕ) (hA : ∀ i j, (A i j).natDegree ≤ e i)
    (hL : Function.Injective (Matrix.mulVec
      ((Matrix.of fun i k => (A i k).coeff (e i)).transpose)))
    (hp : ∀ d : K[X], (∀ r : Fin N → Fin (N+1), d ∣ (A.submatrix id r).det) → IsUnit d) :
    HasMinimalKernelDegrees A [∑ i, e i] := by
  apply hasMinimalKernelDegrees_singleton_of_generator A (rectangularCofactors A.transpose)
    (by simpa only [Matrix.transpose_transpose] using rectangularCofactors_relation A.transpose)
    (fun y => ?_) _ (right_rectangularCofactor_degree A e hA)
    (right_rectangularCofactors_nonzero_top A e hA hL)
  simpa only [Matrix.transpose_transpose] using
    rectangularCofactors_kernel_iff_unique_of_maximal_minors_units A.transpose
      (fun d hd => hp d (fun r => by
        have hh := hd r
        have he : A.transpose.submatrix r id = (A.submatrix id r).transpose := rfl
        simpa only [he,Matrix.det_transpose] using hh)) y

end FD56
