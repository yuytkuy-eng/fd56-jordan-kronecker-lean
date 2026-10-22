/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedSurjectivity

/-! Balanced left-kernel dimensions imply coefficient surjectivity once
the source dimension is at least the target dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r : Type*} [Field K] [Fintype m] [Fintype r]
  [DecidableEq m] [DecidableEq r]

omit [Fintype r] [DecidableEq m] [DecidableEq r] in
theorem weighted_uniform_kernel (P : Matrix r m K[X]) (d : ℕ) :
    weightedPolynomialKernel P (fun _ => d) = polynomialKernelAtDegree P d := rfl

omit [DecidableEq r] in
theorem column_coefficient_surjective_of_kernel_hilbert
    (G : Matrix m r K[X]) (δ : r → ℕ) (d : ℕ)
    (hG : ∀ j i, (G j i).natDegree ≤ δ i)
    (hrm : Fintype.card r ≤ Fintype.card m)
    (hd : ∑ i, δ i ≤ (Fintype.card m - Fintype.card r) * (d + 1))
    (hh : Module.finrank K (polynomialKernelAtDegree G.transpose d) =
      (Fintype.card m - Fintype.card r) * (d + 1) - ∑ i, δ i) :
    Function.Surjective (weightedCoefficientMatrix G.transpose
      (fun _ => d) (fun i => d + δ i)).mulVec := by
  apply weighted_coefficient_surjective_of_kernel_finrank
  · intro i j
    change (G j i).natDegree + d ≤ d + δ i
    have := hG j i
    omega
  · rw [weighted_uniform_kernel, hh]
    simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul]
    have hm : Fintype.card m = Fintype.card r + (Fintype.card m - Fintype.card r) := by omega
    have hs := Nat.sub_add_cancel hd
    nlinarith

end FD56
