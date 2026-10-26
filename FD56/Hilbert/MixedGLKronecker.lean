/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedKroneckerCanonical
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.CorankOneKirillov
import FD56.Hilbert.ThirteenFourKirillov

/-! Constant congruences for GL pencils with a complete list of Kronecker degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def HasKroneckerDecomposition (P : Matrix n n K[X]) (xs : List ℕ) : Prop :=
  ∃ (r : ℕ) (d : Fin r → ℕ), (List.ofFn d).Perm xs ∧
  ∃ T : Matrix n (Σ j, Fin (d j) ⊕ Fin (d j + 1)) K,
  ∃ S : Matrix (Σ j, Fin (d j) ⊕ Fin (d j + 1)) n K,
    T * S = 1 ∧ S * T = 1 ∧
    (T.map C).transpose * P * T.map C =
      Matrix.blockDiagonal' (fun j : Fin r => kroneckerBlockPencil (K := K) (d j))

theorem glKirillovMatrix_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (xs : List ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hmin : HasMinimalKernelDegrees (glEquationMatrix M P) xs)
    (hcard : Fintype.card (SLInput n m) = (xs.map (fun e => 2 * e + 1)).sum) :
    HasKroneckerDecomposition (glKirillovMatrix M P) xs := by
  let A := fun i j => (glKirillovMatrix M P i j).coeff 0
  let B := fun i j => (glKirillovMatrix M P i j).coeff 1
  have he : affineMatrixPencil A B = glKirillovMatrix M P :=
    affineMatrixPencil_coefficients _ (glKirillovMatrix_degreeBound M P 1 hM hP)
  have hm : HasMinimalKernelDegrees (affineMatrixPencil A B) xs := by
    rw [he]
    exact (glKirillovMatrix_hasMinimalKernelDegrees_iff M P _).mpr hmin
  obtain ⟨r, d, hp, T, S, hTS, hST, hc⟩ := exists_mixed_kronecker_canonical A B xs hm hcard
    (glKirillovMatrix_coefficient_skew M P 0)
    (glKirillovMatrix_coefficient_skew M P 1)
    (glKirillovMatrix_coefficient_alternating M P 0)
    (glKirillovMatrix_coefficient_alternating M P 1)
  exact ⟨r, d, hp, T, S, hTS, hST, he ▸ hc⟩

variable {m t : Type*} [Fintype m] [DecidableEq m]
  [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_corank_one_repeated_gl_kronecker_decomposition
    (hm : 2 ≤ Fintype.card m) (hn : Fintype.card n + 1 = 4 * Fintype.card m) :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (n × t) (m × t)) (genericAffineRows K (n × t) (m × t)))
      ((balancedDegreeList (6 * Fintype.card (m × t))
        (Fintype.card (n × t) - 3 * Fintype.card (m × t))).flatMap
          (fun a => List.replicate (Fintype.card t) (a + (10 * Fintype.card m - 1)))) := by
  exact glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    (generic_corank_one_repeated_depth_three_gl_minimal_degrees hm hn)
    (corank_one_repeated_kirillov_dimension_budget hm hn).symm

theorem generic_thirteen_four_repeated_gl_kronecker_decomposition [CharZero K] :
    HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 13 × t) (Fin 4 × t))
      (genericAffineRows K (Fin 13 × t) (Fin 4 × t)))
      (List.replicate (2 * Fintype.card t ^ 2) 36 ++
        List.replicate (Fintype.card t ^ 2) 37) := by
  exact glKirillovMatrix_kronecker _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_thirteen_four_repeated_gl_minimal_degrees
    thirteen_four_repeated_kirillov_dimension_budget.symm

end FD56
