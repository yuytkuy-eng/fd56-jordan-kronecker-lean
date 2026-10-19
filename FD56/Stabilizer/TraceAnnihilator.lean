/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Kirillov

/-! The trace pairing is nondegenerate, and the annihilator of traceless
matrices consists exactly of scalar matrices. These statements hold over
commutative rings and give the full SL stabilizer equations over K[X]. -/

noncomputable section
open Matrix Polynomial
namespace FD56

variable {R : Type*} [CommRing R]
variable {m n : Type*} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

theorem trace_mul_matrix_unit (A : Matrix m n R) (i : n) (j : m) :
    Matrix.trace (A * Matrix.stdBasisMatrix i j (1 : R)) = A j i := by
  simp [Matrix.trace, Matrix.mul_apply, Matrix.stdBasisMatrix, Matrix.diag, ite_and]

theorem trace_pairing_nondegenerate (A : Matrix m n R)
    (h : ∀ B : Matrix n m R, Matrix.trace (A * B) = 0) : A = 0 := by
  ext j i
  simpa only [trace_mul_matrix_unit] using h (Matrix.stdBasisMatrix i j 1)

theorem trace_zero_annihilator [Nonempty n] (A : Matrix n n R) :
    (∀ Y : Matrix n n R, Matrix.trace Y = 0 → Matrix.trace (A * Y) = 0) ↔
      ∃ c : R, A = c • (1 : Matrix n n R) := by
  constructor
  · intro h
    let i₀ : n := Classical.choice inferInstance
    have hoff : ∀ i j, i ≠ j → A i j = 0 := by
      intro i j hij
      have ht : Matrix.trace (Matrix.stdBasisMatrix j i (1 : R)) = 0 := by
        exact Matrix.StdBasisMatrix.trace_zero j i 1 hij
      simpa only [trace_mul_matrix_unit] using h _ ht
    have hdiag : ∀ i, A i i = A i₀ i₀ := by
      intro i
      have ht : Matrix.trace (Matrix.stdBasisMatrix i i (1 : R) -
          Matrix.stdBasisMatrix i₀ i₀ (1 : R)) = 0 := by
        simp
      have hh := h _ ht
      rw [Matrix.mul_sub, Matrix.trace_sub, trace_mul_matrix_unit,
        trace_mul_matrix_unit] at hh
      exact sub_eq_zero.mp hh
    refine ⟨A i₀ i₀, ?_⟩
    ext i j
    by_cases hij : i = j
    · subst j
      simpa using hdiag i
    · simp [hoff i j hij, Matrix.one_apply, hij]
  · rintro ⟨c, rfl⟩ Y hY
    simp [Matrix.smul_mul, Matrix.trace_smul, hY]

variable {K : Type*} [Field K]

/-- Exact equations for the full radical, including the scalar correction. -/
theorem slRadical_iff_equations [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) :
    SLRadical M P X U ↔ Matrix.trace X = 0 ∧ P * X = 0 ∧
      ∃ c : K[X], M * X - X * M = U * P + c • (1 : Matrix n n K[X]) := by
  constructor
  · rintro ⟨hT, h⟩
    have hP : P * X = 0 := by
      apply trace_pairing_nondegenerate
      intro W
      have hh := h 0 W (by simp)
      simpa [kirillov_equations] using hh
    have hA : ∀ Y : Matrix n n K[X], Matrix.trace Y = 0 →
        Matrix.trace ((M * X - X * M - U * P) * Y) = 0 := by
      intro Y hY
      have hh := h Y 0 hY
      simpa [kirillov_equations] using hh
    obtain ⟨c, hc⟩ := (trace_zero_annihilator _).mp hA
    refine ⟨hT, hP, c, ?_⟩
    exact (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)
  · rintro ⟨hT, hP, c, hc⟩
    refine ⟨hT, ?_⟩
    intro Y W hY
    rw [kirillov_equations, hc, add_sub_cancel_left, hP]
    simp [Matrix.smul_mul, Matrix.trace_smul, hY]

end FD56
