/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericSquareSLDecomposition
import FD56.Stabilizer.SquareSLCanonicalTarget

/-! Complete generic square SL canonical decomposition: one Kronecker block
of minimal degree n-1, and n-1 simple Jordan blocks at each of n distinct poles. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable (K n : Type*) [Field K] [Fintype n] [DecidableEq n] [Nontrivial n]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem generic_square_sl_jordan_kronecker_decomposition (i₀ : n) :
    ∃ lam : n → GenericSquareGLSplittingField K n, Function.Injective lam ∧
    ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLChartInput n n i₀) (squareSLCanonicalIndex j) (GenericSquareGLSplittingField K n),
    ∃ H : Matrix (squareSLCanonicalIndex j) (SLChartInput n n i₀) (GenericSquareGLSplittingField K n),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose *
          (slKirillovMatrix (genericAffineSquare K n n) (genericAffineRows K n n) i₀).map
            (Polynomial.mapRingHom (genericSquareGLFieldEmbedding K n)) * G.map C =
        squareSLCanonicalTarget lam j := by
  obtain ⟨lam,hlam,j,hj,G,H,hGH,hHG,hcong⟩ := generic_square_sl_separated_decomposition K n i₀
  refine ⟨lam,hlam,j,hj,?_⟩
  simp_rw [slKirillovMatrix_map] at hcong ⊢
  exact squareSL_canonical_of_separated _ _ lam hlam j i₀ G H hGH hHG hcong

end FD56
