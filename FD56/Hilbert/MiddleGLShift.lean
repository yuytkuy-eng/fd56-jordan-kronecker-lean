/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleGL
import FD56.Hilbert.MinimalBasis

/-! Shifted auxiliary Hilbert values determine a bounded middle GL kernel
without requiring a prescribed degree list for the left auxiliary kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n m r : Type*} [Field K] [Fintype n] [Fintype m] [Fintype r]
  [DecidableEq n] [DecidableEq m] [DecidableEq r]

theorem middle_gl_kernel_hilbert_shifted
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' P)))
    (R : Matrix n m K[X]) (hPR : P * R = 1)
    (hG : Function.Injective (P * M * polynomialKernelBasisMatrix P B).mulVec)
    (a : r → ℕ) (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hV : ∀ x i, (polynomialKernelBasisMatrix P B x i).natDegree ≤ a i)
    (hVlead : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix P B x i).coeff (a i))))
    (hPlead : Function.Injective (matrixCoeff P 1).transpose.mulVec)
    (d : ℕ) (hd : ∀ i, a i + 1 ≤ d) :
    Module.finrank K (polynomialKernelAtDegree (glEquationMatrix M P) d) =
      ∑ i, Module.finrank K (polynomialKernelAtDegree
        (P * M * polynomialKernelBasisMatrix P B).transpose (d - (a i + 1))) := by
  obtain ⟨s, Bt, b, hT, hTL, _, hH⟩ := polynomial_kernel_has_minimal_basis
    (P * M * polynomialKernelBasisMatrix P B).transpose
  rw [middle_gl_kernel_hilbert_of_bases M P B Bt R hPR hG a b
    hM hP hV hT hVlead hTL hPlead d, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i _
  rw [hH]
  apply Finset.sum_congr rfl
  intro j _
  change d + 1 - (a i + b j + 1) = d - (a i + 1) + 1 - b j
  have := hd i
  omega

end FD56
