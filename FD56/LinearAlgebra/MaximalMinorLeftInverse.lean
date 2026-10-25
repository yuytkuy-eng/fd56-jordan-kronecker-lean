/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RectangularCofactors
import FD56.LinearAlgebra.KernelDescent

/-! A left inverse from maximal minors with only unit common divisors. -/

namespace FD56
open Matrix

variable {R b k : Type*} [CommRing R] [IsPrincipalIdealRing R]
  [Fintype b] [Fintype k] [DecidableEq k]

theorem left_inverse_of_unit_common_maximal_divisors (A : Matrix b k R)
    (h : ∀ d : R, (∀ r : k → b, d ∣ (A.submatrix r id).det) → IsUnit d) :
    ∃ L : Matrix k b R, L * A = 1 := by
  classical
  obtain ⟨w, hw⟩ := bezout_of_common_divisors_are_units
    (fun r : k → b => (A.submatrix r id).det) h
  let E : (k → b) → Matrix k b R := fun r => (1 : Matrix b b R).submatrix r id
  have hE (r : k → b) : E r * A = A.submatrix r id := by
    simpa only [E, Equiv.refl_apply, Function.id_comp] using
      Matrix.one_submatrix_mul r (Equiv.refl b) A
  apply left_inverse_of_bezout A E w
  simpa only [hE] using hw

end FD56
