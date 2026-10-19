/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLSpace
import FD56.LinearAlgebra.PolynomialBezout
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! The terminal case of GL block reduction, with a full-column-rank matrix. -/

noncomputable section
namespace FD56
open Matrix
variable {K m r : Type*} [Field K] [Fintype m] [Fintype r] [DecidableEq r]

def rightMultiplication (B : Matrix m r K) :
    Matrix r m K →ₗ[K] Matrix r r K where
  toFun E := E * B
  map_add' := fun E F => Matrix.add_mul E F B
  map_smul' := fun c E => Matrix.smul_mul c E B

theorem rightMultiplication_surjective (B : Matrix m r K) (L : Matrix r m K)
    (hL : L * B = 1) : Function.Surjective (rightMultiplication B) := by
  intro H
  refine ⟨H * L, ?_⟩
  change (H * L) * B = H
  rw [Matrix.mul_assoc, hL, Matrix.mul_one]

def glBaseEquiv (D : Matrix r r K) (B : Matrix m r K) (L : Matrix r m K)
    (hL : L * B = 1) :
    glStabilizerSpace D B ≃ₗ[K] LinearMap.ker (rightMultiplication B) where
  toFun z := ⟨z.val.2, by
    have hz := z.property
    change B * z.val.1 = 0 ∧ D * z.val.1 - z.val.1 * D = z.val.2 * B at hz
    have hG : z.val.1 = 0 := by
      have h := congrArg (fun T => L * T) hz.1
      simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_zero] using h
    change z.val.2 * B = 0
    simpa only [hG, Matrix.mul_zero, Matrix.zero_mul, sub_self] using hz.2.symm⟩
  invFun E := ⟨(0, E.val), by
    change B * 0 = 0 ∧ D * 0 - 0 * D = E.val * B
    have hE : E.val * B = 0 := E.property
    simp [hE]⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · have hz : B * z.val.1 = 0 := z.property.1
      have h := congrArg (fun T => L * T) hz
      simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_zero] using h.symm
    · rfl
  right_inv E := by apply Subtype.ext; rfl
  map_add' z w := by apply Subtype.ext; rfl
  map_smul' c z := by apply Subtype.ext; rfl

theorem gl_base_finrank (D : Matrix r r K) (B : Matrix m r K) (L : Matrix r m K)
    (hL : L * B = 1) :
    Module.finrank K (glStabilizerSpace D B) =
      Fintype.card r * (Fintype.card m - Fintype.card r) := by
  have hs := rightMultiplication_surjective B L hL
  have hd := (rightMultiplication B).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs, finrank_top,
    Module.finrank_matrix, Module.finrank_matrix] at hd
  simp only [Module.finrank_self, mul_one] at hd
  rw [(glBaseEquiv D B L hL).finrank_eq]
  rw [Nat.mul_sub_left_distrib]
  omega

theorem gl_base_finrank_of_injective [DecidableEq m]
    (D : Matrix r r K) (B : Matrix m r K) (hB : Function.Injective B.mulVec) :
    Module.finrank K (glStabilizerSpace D B) =
      Fintype.card r * (Fintype.card m - Fintype.card r) := by
  obtain ⟨L, hL⟩ := matrix_left_inverse_of_injective B hB
  exact gl_base_finrank D B L hL

end FD56
