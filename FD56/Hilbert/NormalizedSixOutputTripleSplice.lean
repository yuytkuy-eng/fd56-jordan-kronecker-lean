/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleSpliceNormalization
import FD56.Hilbert.SixOutputThreeColumnTailWitness

/-! The certified degree-five tail gives a normalized three-column splice. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

variable {K F : Type*} [Field K] [CharZero K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]

theorem normalized_six_output_triple_splice_kernel_finrank_le
    (G : Matrix (Fin 6) (Fin 3) K[X])
    (hG : ∀ i j, (G i j).coeff 0=sixOutputTripleBaseFrame K i j) (d : ℕ) :
    Module.finrank F (polynomialKernelAtDegree
      ((sixOutputTripleSpliceTangent G sixOutputThreeColumnTailFrame 5).map
        (Polynomial.mapRingHom (algebraMap K[X] F))) (d+6)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) := by
  apply six_output_triple_tangent_splice_kernel_finrank_le
    G sixOutputThreeColumnTailFrame 5 6 d (by omega) sixOutputThreeColumnTailFrame_degree
  · intro i j
    rw [sixOutputThreeColumnTailFrame_top,hG i j]
    rfl
  · exact sixOutputThreeColumnTail_bounded_kernel_zero_charZero

theorem normalized_six_output_triple_splice_step
    (G : Matrix (Fin 6) (Fin 3) K[X]) (a : ℕ)
    (hG : ∀ i j, (G i j).coeff 0=sixOutputTripleBaseFrame K i j)
    (hdG : ∀ i j, (G i j).natDegree≤a) :
    ∃ G' : Matrix (Fin 6) (Fin 3) F[X],
      (∀ i j, (G' i j).coeff 0=sixOutputTripleBaseFrame F i j) ∧
      (∀ i j, (G' i j).natDegree≤a+5) ∧
      ∀ d, Module.finrank F (polynomialKernelAtDegree
        (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G')) (d+6)) ≤
        Module.finrank K (polynomialKernelAtDegree
          (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) := by
  apply normalized_six_output_triple_splice_step_of_tail sixOutputThreeColumnTailFrame
    sixOutputThreeColumnTailFrame_degree sixOutputThreeColumnTailFrame_constant
  · intro i j
    exact sixOutputThreeColumnTailFrame_top i j
  · exact sixOutputThreeColumnTail_bounded_kernel_zero_charZero
  · exact hG
  · exact hdG

end FD56
