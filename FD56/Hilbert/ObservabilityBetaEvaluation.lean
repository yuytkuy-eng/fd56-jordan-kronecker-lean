/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityBetaCoefficients
import FD56.Hilbert.WeightedKernelGrowth
import FD56.Hilbert.GenericTerminalObservability
import FD56.LinearAlgebra.RowNormalization

/-! Growth of bounded auxiliary relations from terminal observability alone. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]
  [DecidableEq m] [DecidableEq n]

theorem observabilityBetaEquationMatrix_eval_surjective (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (x : K)
    (hO : Function.Injective ((observabilityMatrix M P (q+1)).map
      (Polynomial.evalRingHom x)).mulVec) :
    Function.Surjective ((observabilityBetaEquationMatrix q M P).map
      (Polynomial.evalRingHom x)).mulVec := by
  let C := (observabilityMatrix M P (q+1)).map (Polynomial.evalRingHom x)
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective C hO
  have ht : Function.Surjective C.transpose.mulVec := by
    intro v
    refine ⟨L.transpose *ᵥ v,?_⟩
    rw [Matrix.mulVec_mulVec,← Matrix.transpose_mul,hL,Matrix.transpose_one,Matrix.one_mulVec]
  intro v
  obtain ⟨w,hw⟩ := ht v
  refine ⟨Sum.elim (fun j => w (Fin.last q,j)) (fun i => -w (i.1.castSucc,i.2)),?_⟩
  rw [← hw]
  funext j
  simp only [observabilityBetaEquationMatrix,Matrix.map_apply,Matrix.mulVec,dotProduct,
    Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,map_neg,neg_mul_neg,
    C,Matrix.transpose_apply,observabilityMatrix,Fintype.sum_prod_type,
    Fin.sum_univ_castSucc,Fin.val_last,Fin.coe_castSucc]
  rw [add_comm]

theorem boundedObservabilityBetaKernel_growth (q : ℕ)
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hO : Function.Injective ((observabilityMatrix M P (q+1)).map
      (Polynomial.evalRingHom 0)).mulVec) (d : ℕ) :
    Module.finrank K (boundedObservabilityBetaKernel q M P (d+1)) ≤
      Module.finrank K (boundedObservabilityBetaKernel q M P d) +
        ((q+1)*Fintype.card m-Fintype.card n) := by
  have hd := surjective_matrix_kernel_finrank _
    (observabilityBetaEquationMatrix_eval_surjective q M P 0 hO)
  have hg : observabilityBetaDegrees (m := m) q (d+1) =
      fun j => observabilityBetaDegrees q d j+1 := by
    funext j
    cases j with
    | inl j => rfl
    | inr j =>
      simp only [observabilityBetaDegrees,Sum.elim_inr,observabilityBetaCoefficientDegree]
      have := j.1.isLt
      omega
  have hh := weighted_polynomial_kernel_growth (observabilityBetaEquationMatrix q M P)
    (observabilityBetaDegrees q d)
  have he := congrArg (fun g : m ⊕ (Fin q × m) → ℕ =>
    Module.finrank K (weightedPolynomialKernel (observabilityBetaEquationMatrix q M P) g)) hg
  dsimp only at he
  rw [← he,(observabilityBetaWeightedKernelEquiv q M P (d+1)).finrank_eq,
    (observabilityBetaWeightedKernelEquiv q M P d).finrank_eq,hd] at hh
  simpa only [Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,
    Nat.add_mul,Nat.one_mul,Nat.add_comm] using hh

theorem generic_bounded_observability_beta_growth (q : ℕ)
    (hlo : q*Fintype.card m ≤ Fintype.card n)
    (hhi : Fintype.card n ≤ (q+1)*Fintype.card m) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m) (genericAffineRows K n m) (d+1)) ≤
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedObservabilityBetaKernel q (genericAffineSquare K n m) (genericAffineRows K n m) d) +
        ((q+1)*Fintype.card m-Fintype.card n) :=
  boundedObservabilityBetaKernel_growth q _ _
    (generic_terminal_observability_zero_injective q hlo hhi) d

end FD56
