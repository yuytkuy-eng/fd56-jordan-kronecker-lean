/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile
import FD56.Hilbert.GenericAbove
import FD56.Hilbert.Square

/-! The generic Hilbert formulas are realized by actual reduced polynomial
kernel bases. These statements specify minimal degrees, not regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def balancedDegreeList (degree count : ℕ) : List ℕ :=
  List.replicate (degree % count) (degree / count + 1) ++
    List.replicate (count - degree % count) (degree / count)

theorem balancedDegreeList_hilbert (degree count d : ℕ) (hcount : 0 < count) :
    ((balancedDegreeList degree count).map (fun e => d + 1 - e)).sum =
      count * (d + 1) - degree := by
  simpa [balancedDegreeList, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate] using
      rectangular_balanced_hilbert_sizes degree count d hcount

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_rows_minimal_degrees (hmn : Fintype.card m < Fintype.card n) :
    HasMinimalKernelDegrees (genericAffineRows K n m)
      (balancedDegreeList (Fintype.card m) (Fintype.card n - Fintype.card m)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_rows_kernel_hilbert hmn d, balancedDegreeList_hilbert _ _ d (by omega)]

theorem generic_above_gl_minimal_degrees (hnm : Fintype.card n < Fintype.card m) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m))
      (List.replicate (Fintype.card n * (Fintype.card n % (Fintype.card m - Fintype.card n)))
        (Fintype.card n / (Fintype.card m - Fintype.card n) + 1) ++
      List.replicate (Fintype.card n * ((Fintype.card m - Fintype.card n) -
        Fintype.card n % (Fintype.card m - Fintype.card n)))
        (Fintype.card n / (Fintype.card m - Fintype.card n))) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_above_gl_kernel_hilbert hnm d]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    smul_eq_mul, mul_assoc, ← mul_add]
  rw [rectangular_balanced_hilbert_sizes _ _ d (by omega)]

theorem generic_above_sl_minimal_degrees (i₀ : n)
    (hnm : Fintype.card n < Fintype.card m) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
      (balancedDegreeList (Fintype.card n * Fintype.card n - 1)
        (Fintype.card n * (Fintype.card m - Fintype.card n) + 1)) := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel _ _ i₀, generic_above_slHilbert i₀ hnm d,
    balancedDegreeList_hilbert _ _ d (by omega)]

theorem generic_square_sl_minimal_degrees (n : ℕ) (hn : 0 < n) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin n)) (genericAffineRows K (Fin n) (Fin n)) ⟨0, hn⟩)
      [n - 1] := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [← slHilbert_eq_matrix_kernel (genericAffineSquare K (Fin n) (Fin n))
    (genericAffineRows K (Fin n) (Fin n)) (⟨0, hn⟩ : Fin n), generic_square_slHilbert n hn d]
  simp

theorem generic_square_gl_minimal_degrees (n : ℕ) :
    HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K (Fin n) (Fin n)) (genericAffineRows K (Fin n) (Fin n))) [] := by
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_square_gl_kernel_hilbert n d]
  rfl

end FD56
