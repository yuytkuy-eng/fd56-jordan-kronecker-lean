/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLSpace

/-! Stabilizer spaces and their trace condition are invariant under a change
of coordinates on the defining representation. -/

noncomputable section
namespace FD56
open Matrix
variable {R n m p : Type*} [CommRing R] [Fintype n] [Fintype m] [Fintype p]
  [DecidableEq n] [DecidableEq p]

omit [DecidableEq p] in
theorem gl_change_basis_mem (M : Matrix n n R) (P : Matrix m n R)
    (S : Matrix n p R) (I : Matrix p n R) (hSI : S * I = 1)
    (z : Matrix n n R × Matrix n m R) (hz : z ∈ glStabilizerSpace M P) :
    (I * z.1 * S, I * z.2) ∈ glStabilizerSpace (I * M * S) (P * S) := by
  constructor
  · change (P * S) * (I * z.1 * S) = 0
    calc
      _ = (P * z.1) * S := by
        simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S I, hSI, Matrix.one_mul]
      _ = 0 := by rw [hz.1, Matrix.zero_mul]
  · change (I * M * S) * (I * z.1 * S) - (I * z.1 * S) * (I * M * S) =
        (I * z.2) * (P * S)
    have h := congrArg (fun A => I * A * S) hz.2
    simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc S I, hSI, Matrix.one_mul] using h

def glChangeBasisEquiv (M : Matrix n n R) (P : Matrix m n R)
    (S : Matrix n p R) (I : Matrix p n R) (hSI : S * I = 1) (hIS : I * S = 1) :
    glStabilizerSpace M P ≃ₗ[R] glStabilizerSpace (I * M * S) (P * S) where
  toFun z := ⟨(I * z.val.1 * S, I * z.val.2), gl_change_basis_mem M P S I hSI z.val z.property⟩
  invFun z := ⟨(S * z.val.1 * I, S * z.val.2), by
    have h := gl_change_basis_mem (I * M * S) (P * S) I S hIS z.val z.property
    have hM : S * (I * M * S) * I = M := by
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S I, hSI, Matrix.one_mul,
        ← Matrix.mul_assoc M S, hSI, Matrix.mul_one]
    have hP : (P * S) * I = P := by rw [Matrix.mul_assoc, hSI, Matrix.mul_one]
    simpa only [hM, hP] using h⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change S * (I * z.val.1 * S) * I = z.val.1
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc S I, hSI, Matrix.one_mul,
        ← Matrix.mul_assoc z.val.1 S, hSI, Matrix.mul_one]
    · change S * (I * z.val.2) = z.val.2
      rw [← Matrix.mul_assoc, hSI, Matrix.one_mul]
  right_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · change I * (S * z.val.1 * I) * S = z.val.1
      simp only [Matrix.mul_assoc, ← Matrix.mul_assoc I S, hIS, Matrix.one_mul,
        ← Matrix.mul_assoc z.val.1 I, hIS, Matrix.mul_one]
    · change I * (S * z.val.2) = z.val.2
      rw [← Matrix.mul_assoc, hIS, Matrix.one_mul]
  map_add' z w := by
    apply Subtype.ext
    apply Prod.ext <;> simp [Matrix.mul_add, Matrix.add_mul]
  map_smul' c z := by
    apply Subtype.ext
    apply Prod.ext <;> simp [Matrix.mul_smul, Matrix.smul_mul]

theorem gl_change_basis_finrank (M : Matrix n n R) (P : Matrix m n R)
    (S : Matrix n p R) (I : Matrix p n R) (hSI : S * I = 1) (hIS : I * S = 1) :
    Module.finrank R (glStabilizerSpace (I * M * S) (P * S)) =
      Module.finrank R (glStabilizerSpace M P) :=
  (glChangeBasisEquiv M P S I hSI hIS).finrank_eq.symm

omit [DecidableEq p] in
theorem gl_change_basis_trace (S : Matrix n p R) (I : Matrix p n R)
    (X : Matrix n n R) (hSI : S * I = 1) :
    Matrix.trace (I * X * S) = Matrix.trace X := by
  rw [Matrix.trace_mul_cycle, hSI, Matrix.one_mul]

end FD56
