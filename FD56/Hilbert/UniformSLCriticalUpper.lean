/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformSLCriticalBound

/-! Scalar coefficient selectors bound the actual uniform critical radical. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

def constantSLRelationSelector (G : Matrix m r K[X]) (b : ℕ) (hG : DegreeBound G b)
    (t : ℕ) (f : Fin t → ℕ) :
    LinearMap.ker (constantSLRelation G b hG) →ₗ[K] (Fin t → K) where
  toFun z j := z.val.2.val.coeff (f j)
  map_add' z w := by ext j; exact Polynomial.coeff_add _ _ _
  map_smul' k z := by ext j; exact Polynomial.coeff_smul _ _ _

omit [Fintype r] [DecidableEq m] in
theorem constantSLRelationSelector_injective
    (G : Matrix m r K[X]) (b : ℕ) (hG : DegreeBound G b) (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E 0 →
      E * G = (-c) • 1 → (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    Function.Injective (constantSLRelationSelector G b hG t f) := by
  intro x y hxy
  suffices h : x - y = 0 by exact sub_eq_zero.mp h
  let z := x - y
  have hz : constantSLRelationSelector G b hG t f z = 0 := by
    dsimp only [z]
    exact ((constantSLRelationSelector G b hG t f).map_sub x y).trans
      (by rw [hxy, sub_self])
  have hc : ∀ j, z.val.2.val.coeff (f j) = 0 := congrFun hz
  have hh := hzero (entries z.val.1) z.val.2.val (entries_degree z.val.1)
    ((constantSLRelation_mem_ker G b hG z.val).mp z.property) hc
  change z = 0
  apply Subtype.ext
  apply Prod.ext
  · apply entries_injective 0
    exact hh.1
  · apply Subtype.ext
    exact hh.2

omit [Fintype r] [DecidableEq m] in
theorem constantSLRelation_kernel_upper
    (G : Matrix m r K[X]) (b : ℕ) (hG : DegreeBound G b) (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E 0 →
      E * G = (-c) • 1 → (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    Module.finrank K (LinearMap.ker (constantSLRelation G b hG)) ≤ t := by
  have hh := LinearMap.finrank_le_finrank_of_injective
    (constantSLRelationSelector_injective G b hG t f hzero)
  simpa using hh

theorem uniform_middle_slHilbert_critical_upper [Nonempty n]
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1) (a : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hB : DegreeBound (polynomialKernelBasisMatrix P B) a)
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec) (j₀ : r)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (hBL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff a)))
    (t : ℕ) (f : Fin t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]), DegreeBound E 0 →
      E * (P * M * polynomialKernelBasisMatrix P B) = (-c) • 1 →
      (∀ j, c.coeff (f j) = 0) → E = 0 ∧ c = 0) :
    slHilbert M P (a + 1) ≤ t := by
  rw [uniform_middle_slHilbert_critical_eq M P B R hPR a hM hP hB hPlead j₀ hG hBL]
  exact constantSLRelation_kernel_upper _ _ _ t f hzero

end FD56
