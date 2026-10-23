/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleSLHilbert

/-! One vanishing weighted row eliminates the scalar correction. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem middle_slHilbert_eq_gl_of_column_degree
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hBL : Function.Injective
      (Matrix.mulVec (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPL : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (i₀ : n) (d : ℕ) (j₀ : r) (hd : d ≤ a j₀) :
    slHilbert M P d =
      Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) := by
  apply middle_slHilbert_of_scalar_obstruction M P B R hPR hG a hM hP hB hBL hPL i₀ d
  intro E c hE hrel
  have hrow (j : m) : E j₀ j = 0 := by
    rcases hE j₀ j with h | ⟨h,_⟩
    · exact h
    · omega
  have h := congrArg (fun A : Matrix r r K[X] => A j₀ j₀) hrel
  simpa [Matrix.mul_apply, hrow] using h.symm

end FD56
