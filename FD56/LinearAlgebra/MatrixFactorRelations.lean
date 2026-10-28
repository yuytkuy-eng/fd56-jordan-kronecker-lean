/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Data.Matrix.Mul

/-! Linear relations descend through an injective left matrix factor. -/

namespace FD56
open Matrix

variable {R n r s t : Type*} [CommSemiring R] [Fintype r] [Fintype s]

theorem factor_transpose_kernel_of_product
    (V : Matrix n r R) (C : Matrix r s R) (A : Matrix t s R)
    (hV : Function.Injective V.mulVec) (hAZ : A * (V * C).transpose = 0) :
    A * C.transpose = 0 := by
  have hprod (i : t) : (V * C) *ᵥ A i = 0 := by
    funext k
    simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
      Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using
      congrFun (congrFun hAZ i) k
  have hfactor (i : t) : C *ᵥ A i = 0 := by
    apply hV
    simpa only [Matrix.mulVec_mulVec, Matrix.mulVec_zero] using hprod i
  funext i j
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.zero_apply,
    Matrix.mulVec, dotProduct, Pi.zero_apply, mul_comm] using
    congrFun (hfactor i) j

end FD56
