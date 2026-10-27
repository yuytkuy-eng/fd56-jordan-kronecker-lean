/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLSimplePoleDimension
import FD56.Stabilizer.GLKirillovPencil

/-! Kirillov nullity at a one-dimensional observability defect. -/

noncomputable section
namespace FD56
open Matrix

theorem glKirillovMatrix_field_finrank {K n m : Type*} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (M : Matrix n n K) (P : Matrix m n K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (glKirillovMatrix M P))) =
      Module.finrank K (glStabilizerSpace M P) := by
  have he : LinearMap.ker (Matrix.toLin' (glKirillovMatrix M P)) =
      LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) := by
    ext z
    exact glKirillovMatrix_kernel_iff M P z
  rw [he, glEquationMatrix_field_finrank]

theorem glKirillovMatrix_simple_observability_defect_nullity
    {K : Type*} {n m : Type} [Field K]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (q : ℕ) (M : Matrix n n K) (P : Matrix m n K)
    (hm : 2 ≤ Fintype.card m)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m)
    (hbefore : Module.finrank K (unobservableSpace M P q) = Fintype.card m)
    (hfirst : Module.finrank K (unobservableSpace M P (q + 1)) = 1)
    (hnext : Module.finrank K (unobservableSpace M P (q + 2)) = 0) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (glKirillovMatrix M P))) =
      2 * Fintype.card m - 2 := by
  rw [glKirillovMatrix_field_finrank]
  exact gl_finrank_of_simple_observability_defect q M P hm hsize hbefore hfirst hnext

end FD56
