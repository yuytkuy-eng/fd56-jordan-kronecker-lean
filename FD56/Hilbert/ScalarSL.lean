/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HilbertObstruction

/-! For a one-dimensional square component the special linear algebra is
zero. Every translation is radical, for every polynomial pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K m : Type*} [Field K] [Fintype m]

theorem scalar_slRadical_iff (M X : Matrix Unit Unit K[X])
    (P : Matrix m Unit K[X]) (U : Matrix Unit m K[X]) :
    SLRadical M P X U ↔ X = 0 := by
  have ht (A : Matrix Unit Unit K[X]) : Matrix.trace A = 0 ↔ A = 0 := by
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_unique]
    constructor
    · intro h
      funext i j
      cases i; cases j
      exact h
    · intro h
      simp [h]
  constructor
  · intro h
    exact (ht X).mp h.1
  · intro h
    refine ⟨(ht X).mpr h, ?_⟩
    intro Y W hY
    have hy := (ht Y).mp hY
    simp [kirillov, h, hy]

def scalarSLKernelEquiv (M : Matrix Unit Unit K[X]) (P : Matrix m Unit K[X]) (d : ℕ) :
    boundedSLKernel M P d ≃ₗ[K] BoundedMatrix K Unit m d where
  toFun z := z.val.2
  invFun U := ⟨(0, U), (scalar_slRadical_iff M _ P _).mpr rfl⟩
  left_inv z := by
    apply Subtype.ext
    apply Prod.ext
    · have h := (scalar_slRadical_iff M _ P _).mp z.property
      funext i j
      apply Subtype.ext
      exact (congrArg (fun A => A i j) h).symm
    · rfl
  right_inv U := rfl
  map_add' z w := rfl
  map_smul' c z := rfl

theorem scalar_slHilbert (M : Matrix Unit Unit K[X]) (P : Matrix m Unit K[X]) (d : ℕ) :
    slHilbert M P d = Fintype.card m * (d + 1) := by
  unfold slHilbert
  rw [(scalarSLKernelEquiv M P d).finrank_eq, boundedMatrix_finrank]
  simp

theorem scalar_slHilbert_profile (M : Matrix Unit Unit K[X]) (P : Matrix m Unit K[X]) :
    HasHilbertProfile M P (fun _ : m => 0) := by
  intro d
  rw [scalar_slHilbert]
  simp [profile]

end FD56
