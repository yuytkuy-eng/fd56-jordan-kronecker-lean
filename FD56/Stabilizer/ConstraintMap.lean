/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.TraceAnnihilator

/-! A finite linear constraint map for the full SL radical.
Subtracting one diagonal entry removes the existential scalar correction. -/

noncomputable section
namespace FD56
open Polynomial Matrix
variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def stabilizerResidual (M : Matrix n n R) (P : Matrix m n R) :
    (Matrix n n R × Matrix n m R) →ₗ[R] Matrix n n R where
  toFun z := M * z.1 - z.1 * M - z.2 * P
  map_add' z w := by
    change M * (z.1 + w.1) - (z.1 + w.1) * M - (z.2 + w.2) * P = _
    simp only [Matrix.mul_add, Matrix.add_mul]
    abel
  map_smul' c z := by
    change M * (c • z.1) - (c • z.1) * M - (c • z.2) * P = _
    simp only [Matrix.mul_smul, Matrix.smul_mul, smul_sub]
    rfl

def scalarCorrectionResidual (i₀ : n) : Matrix n n R →ₗ[R] Matrix n n R where
  toFun A := A - A i₀ i₀ • 1
  map_add' A B := by
    simp only [Matrix.add_apply, add_smul]
    abel
  map_smul' c A := by
    simp only [Matrix.smul_apply, smul_eq_mul, smul_sub, smul_smul]
    rfl

def slConstraintMap (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (Matrix n n R × Matrix n m R) →ₗ[R]
      (R × Matrix m n R × Matrix n n R) where
  toFun z := (Matrix.trace z.1, P * z.1, scalarCorrectionResidual i₀ (stabilizerResidual M P z))
  map_add' z w := by
    apply Prod.ext
    · exact Matrix.trace_add _ _
    · apply Prod.ext
      · exact Matrix.mul_add _ _ _
      · exact map_add ((scalarCorrectionResidual i₀).comp (stabilizerResidual M P)) z w
  map_smul' c z := by
    apply Prod.ext
    · exact Matrix.trace_smul _ _
    · apply Prod.ext
      · exact Matrix.mul_smul _ _ _
      · exact map_smul ((scalarCorrectionResidual i₀).comp (stabilizerResidual M P)) c z

omit [Fintype n] in
theorem scalarCorrectionResidual_eq_zero_iff (i₀ : n) (A : Matrix n n R) :
    scalarCorrectionResidual i₀ A = 0 ↔ ∃ c : R, A = c • (1 : Matrix n n R) := by
  change A - A i₀ i₀ • 1 = 0 ↔ _
  constructor
  · intro h
    exact ⟨A i₀ i₀, sub_eq_zero.mp h⟩
  · rintro ⟨c, rfl⟩
    simp

variable {K : Type*} [Field K]

theorem slConstraintMap_eq_zero_iff (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    slConstraintMap M P i₀ (X, U) = 0 ↔ SLRadical M P X U := by
  letI : Nonempty n := ⟨i₀⟩
  rw [slRadical_iff_equations]
  change (Matrix.trace X, P * X, scalarCorrectionResidual i₀ (M * X - X * M - U * P)) = 0 ↔ _
  simp only [Prod.mk_eq_zero, scalarCorrectionResidual_eq_zero_iff]
  constructor
  · rintro ⟨htr, hp, c, hc⟩
    exact ⟨htr, hp, c, (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)⟩
  · rintro ⟨htr, hp, c, hc⟩
    refine ⟨htr, hp, c, ?_⟩
    rw [hc, add_sub_cancel_left]

end FD56
