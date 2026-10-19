/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.LowDegree

/-! The Kirillov form of the matrix semidirect product and its restriction
to traceless matrices. The definition includes the entire SL radical. -/

noncomputable section
open Matrix Polynomial

namespace FD56
variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [Fintype n]

/-- Pairing (M,P) with the semidirect-product bracket. -/
def kirillov (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (Y : Matrix n n K[X]) (W : Matrix n m K[X]) : K[X] :=
  Matrix.trace (M * (X * Y - Y * X)) + Matrix.trace (P * (X * W - Y * U))

/-- The full radical on the trace-zero subalgebra, with polynomial entries. -/
def SLRadical (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X]) : Prop :=
  Matrix.trace X = 0 ∧ ∀ Y W, Matrix.trace Y = 0 → kirillov M P X U Y W = 0

theorem kirillov_equations (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (Y : Matrix n n K[X]) (W : Matrix n m K[X]) :
    kirillov M P X U Y W =
      Matrix.trace ((M * X - X * M - U * P) * Y) + Matrix.trace ((P * X) * W) := by
  have h1 : Matrix.trace (M * (Y * X)) = Matrix.trace ((X * M) * Y) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle M Y X]
  have h2 : Matrix.trace (P * (Y * U)) = Matrix.trace ((U * P) * Y) := by
    rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle P Y U]
  unfold kirillov
  simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.trace_sub]
  rw [h1, h2]
  simp only [Matrix.mul_assoc]
  ring

theorem strict_stabilizer_mem_radical
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (h : TraceZeroStabilizer M P X U) : SLRadical M P X U := by
  rcases h with ⟨hP, hM, hT⟩
  refine ⟨hT, ?_⟩
  intro Y W _
  rw [kirillov_equations, hM, sub_self, hP]
  simp

theorem kirillov_add (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (X X' : Matrix n n K[X]) (U U' : Matrix n m K[X])
    (Y : Matrix n n K[X]) (W : Matrix n m K[X]) :
    kirillov M P (X + X') (U + U') Y W =
      kirillov M P X U Y W + kirillov M P X' U' Y W := by
  simp only [kirillov, Matrix.add_mul, Matrix.mul_add, Matrix.mul_sub,
    Matrix.trace_add, Matrix.trace_sub]
  ring

theorem kirillov_smul (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (c : K) (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (Y : Matrix n n K[X]) (W : Matrix n m K[X]) :
    kirillov M P (c • X) (c • U) Y W = c • kirillov M P X U Y W := by
  simp only [kirillov, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub,
    Matrix.trace_smul, smul_add]

end FD56
