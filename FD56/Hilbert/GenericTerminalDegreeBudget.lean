/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PrimitiveRowDegreeBudget
import FD56.Hilbert.ObservabilityTerminalLeading
import FD56.LinearAlgebra.DualBasis

/-! The terminal left-kernel degree budget follows from polynomial splitting
and leading independence, without a balancing hypothesis. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem generic_terminal_kernel_degree_budget
    (q : ℕ) (hm : 2≤Fintype.card m)
    (hlo : q*Fintype.card m<Fintype.card n)
    (hhi : Fintype.card n<(q+1)*Fintype.card m)
    (B : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) q))))
    (a : r → ℕ)
    (hV : ∀ i j, (polynomialKernelBasisMatrix _ B i j).natDegree≤a j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix _ B i j).coeff (a j))))
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees
      (genericAffineRows K n m*(genericAffineSquare K n m)^q*
        polynomialKernelBasisMatrix (observabilityMatrix
          (genericAffineSquare K n m) (genericAffineRows K n m) q) B).transpose xs) :
    xs.length+Fintype.card r=Fintype.card m ∧
      xs.sum=(∑ i, a i)+(q+1)*Fintype.card r := by
  let G := genericAffineRows K n m*(genericAffineSquare K n m)^q*
    polynomialKernelBasisMatrix (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) q) B
  obtain ⟨L,hL⟩ := generic_terminal_kernel_left_inverse q hm hlo hhi B
  have hR : G.transpose*L.transpose=1 := by
    rw [← Matrix.transpose_mul,hL,Matrix.transpose_one]
  obtain ⟨hG,hGL⟩ := generic_terminal_kernel_degree_and_leading q hhi.le B a hV hVL
  have hlead : Function.Surjective (show Matrix r m
      (AffineCoefficientField K (MatrixParameters n m)) from
      fun i j => (G.transpose i j).coeff (a i+q+1)).mulVec :=
    matrix_surjective_of_transpose_injective _ hGL
  obtain ⟨hl,hs⟩ := minimal_degree_budget_of_right_inverse_and_leading
    G.transpose L.transpose hR (fun i => a i+q+1) (fun i j => hG j i) hlead xs hmin
  refine ⟨hl,?_⟩
  rw [hs]
  simp only [Nat.add_assoc,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,
    Nat.cast_id]
  ring

end FD56
