/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformKroneckerCanonical
import FD56.Stabilizer.GLKirillovPencil
import FD56.Hilbert.DepthThreeCorankOneRepeatedClassification
import FD56.Hilbert.DepthThreeTenThreeFamily

/-! Actual constant-congruence decompositions for uniform GL families. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

def HasUniformKroneckerDecomposition (P : Matrix n n K[X]) (r e : ℕ) : Prop :=
  ∃ T : Matrix n ((Fin e ⊕ Fin (e + 1)) × Fin r) K,
  ∃ S : Matrix ((Fin e ⊕ Fin (e + 1)) × Fin r) n K,
    T * S = 1 ∧ S * T = 1 ∧
    (T.map C).transpose * P * T.map C =
      Matrix.blockDiagonal (fun _ : Fin r => kroneckerBlockPencil (K := K) e)

theorem glKirillovMatrix_uniform_kronecker {m : Type*} [Fintype m] [DecidableEq m]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (r e : ℕ)
    (hM : DegreeBound M 1) (hP : DegreeBound P 1)
    (hmin : HasMinimalKernelDegrees (glEquationMatrix M P) (List.replicate r e))
    (hcard : Fintype.card (SLInput n m) = r * (2 * e + 1)) :
    HasUniformKroneckerDecomposition (glKirillovMatrix M P) r e := by
  let A := fun i j => (glKirillovMatrix M P i j).coeff 0
  let B := fun i j => (glKirillovMatrix M P i j).coeff 1
  have he : affineMatrixPencil A B = glKirillovMatrix M P :=
    affineMatrixPencil_coefficients _ (glKirillovMatrix_degreeBound M P 1 hM hP)
  have hm : HasMinimalKernelDegrees (affineMatrixPencil A B) (List.replicate r e) := by
    rw [he]
    exact (glKirillovMatrix_hasMinimalKernelDegrees_iff M P _).mpr hmin
  obtain ⟨T, S, hTS, hST, hcanon⟩ := exists_uniform_kronecker_canonical A B hm hcard
    (glKirillovMatrix_coefficient_skew M P 0)
    (glKirillovMatrix_coefficient_skew M P 1)
    (glKirillovMatrix_coefficient_alternating M P 0)
    (glKirillovMatrix_coefficient_alternating M P 1)
  exact ⟨T, S, hTS, hST, he ▸ hcanon⟩

variable {t : Type*} [Fintype t] [DecidableEq t] [Nonempty t]

theorem generic_seven_two_repeated_gl_kronecker_decomposition :
    HasUniformKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 7 × t) (Fin 2 × t))
      (genericAffineRows K (Fin 7 × t) (Fin 2 × t))) (Fintype.card t ^ 2) 31 := by
  apply glKirillovMatrix_uniform_kronecker _ _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_seven_two_repeated_gl_minimal_degrees_all_fields
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem generic_eleven_three_repeated_gl_kronecker_decomposition :
    HasUniformKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 11 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 11 × t) (Fin 3 × t))) (2 * Fintype.card t ^ 2) 38 := by
  apply glKirillovMatrix_uniform_kronecker _ _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_eleven_three_repeated_gl_minimal_degrees_all_fields
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

theorem generic_ten_three_repeated_gl_kronecker_decomposition [CharZero K] :
    HasUniformKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K (Fin 10 × t) (Fin 3 × t))
      (genericAffineRows K (Fin 10 × t) (Fin 3 × t))) (2 * Fintype.card t ^ 2) 32 := by
  apply glKirillovMatrix_uniform_kronecker _ _ _ _
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
    generic_ten_three_repeated_gl_minimal_degrees
  simp only [SLInput, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  ring

end FD56
