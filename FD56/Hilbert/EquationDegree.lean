/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GLMatrix

/-! The coordinate matrices of affine stabilizer equations are affine. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slEquationMatrix_degree (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (i₀ : n) (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (slEquationMatrix M P i₀) 1 := by
  intro a b
  let z := matrixPairEquiv K[X] K[X] n m (fun j => if j = b then 1 else 0)
  have hX : DegreeBound z.1 0 := by
    intro i j
    dsimp [z, matrixPairEquiv]
    split_ifs <;> simp
  have hU : DegreeBound z.2 0 := by
    intro i j
    dsimp [z, matrixPairEquiv]
    split_ifs <;> simp
  have hPX : DegreeBound (P * z.1) 1 := by simpa using degreeBound_mul hP hX
  have hMX : DegreeBound (M * z.1) 1 := by simpa using degreeBound_mul hM hX
  have hXM : DegreeBound (z.1 * M) 1 := by simpa using degreeBound_mul hX hM
  have hUP : DegreeBound (z.2 * P) 1 := by simpa using degreeBound_mul hU hP
  have hA : DegreeBound (stabilizerResidual M P z) 1 :=
    degreeBound_sub (degreeBound_sub hMX hXM) hUP
  rw [slEquationMatrix, LinearMap.toMatrix'_apply]
  rcases a with u | ij | ij
  · change (Matrix.trace z.1).natDegree ≤ 1
    apply Polynomial.natDegree_sum_le_of_forall_le
    intro i _
    exact (hX i i).trans (by omega)
  · exact hPX ij.1 ij.2
  · change ((stabilizerResidual M P z) ij.1 ij.2 -
      (stabilizerResidual M P z) i₀ i₀ * (if ij.1 = ij.2 then 1 else 0)).natDegree ≤ 1
    apply (Polynomial.natDegree_sub_le _ _).trans
    apply max_le (hA ij.1 ij.2)
    by_cases h : ij.1 = ij.2
    · simpa [h] using hA i₀ i₀
    · simp [h]

end FD56
