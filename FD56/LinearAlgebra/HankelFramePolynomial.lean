/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFrameExact

/-! Polynomial exactness obtained by using the indeterminate as the evaluation point. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] [Nontrivial R] {b c : ℕ}

theorem hankelFrame_constant_extension_eval (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (i : Fin c) (w : Fin c ⊕ Fin b) :
    (hankelFrame h g (fun j i r => C (a j i r)) (B.map C) i w).eval X =
      hankelFrame h g a B i w := by
  simp only [hankelFrame,hankelCoefficientPolynomial,eval_add,eval_finset_sum,eval_monomial]
  have hl (s : Fin (g i)) :
      hankelFrameLow h g (fun j i r => C (a j i r)) (B.map C) ⟨i,s⟩ w =
        C (hankelFrameLow h g a B ⟨i,s⟩ w) := by
    cases w <;> simp [hankelFrameLow,Matrix.mul_apply,hankelFrameBoundary,
      Matrix.map_apply,map_sum,map_mul,apply_ite]
  have ht : hankelFrameTop (K := R[X]) i w = C (hankelFrameTop (K := R) i w) := by
    cases w <;> simp [hankelFrameTop,apply_ite]
  simp_rw [hl,ht,C_mul_X_pow_eq_monomial]

def hankelPolynomialKernelParameters (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (v : Fin b → R[X]) : Fin c ⊕ Fin b → R[X] :=
  hankelKernelCoordinates h g (fun j i r => C (a j i r)) (B.map C) X v

theorem hankelFrame_polynomial_exact (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i)
    (x : Fin c ⊕ Fin b → R[X]) :
    hankelFrame h g a B *ᵥ x=0 ↔
      ∃! v : Fin b → R[X], x=hankelPolynomialKernelParameters h g a B v := by
  have hBH' : B.map C * blockHankel h g (fun j i r => C (a j i r))=1 := by
    have he := congrArg (fun M => Matrix.map M (C : R →+* R[X])) hBH
    dsimp only at he
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero C) (map_one C)] at he
    exact he
  have hHB' : blockHankel h g (fun j i r => C (a j i r))*B.map C=1 := by
    have he := congrArg (fun M => Matrix.map M (C : R →+* R[X])) hHB
    dsimp only at he
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero C) (map_one C)] at he
    exact he
  have he := hankelFrame_evaluated_exact h g (fun j i r => C (a j i r))
    (B.map C) hBH' hHB' hh hg X x
  simpa only [Matrix.mulVec,dotProduct,eval_finset_sum,eval_mul,eval_C,
    hankelFrame_constant_extension_eval,hankelPolynomialKernelParameters,
    funext_iff,Pi.zero_apply] using he

end FD56
