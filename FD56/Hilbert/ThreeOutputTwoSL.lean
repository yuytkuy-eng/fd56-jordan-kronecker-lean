/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputTwoSLClosure
import FD56.Hilbert.GenericNondivisibleGLStructure

/-! Complete SL classification for every state count congruent to two modulo three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_three_two_sl_minimal_and_kronecker (q : ℕ) (i₀ : Fin (3*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3)) i₀)
      (List.replicate 3 (threeTwoFrameDegree q)) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3)) i₀)
      (List.replicate 3 (threeTwoFrameDegree q)) := by
  cases q with
  | zero =>
    constructor
    · simpa [threeTwoFrameDegree,balancedDegreeList] using
        generic_above_sl_minimal_degrees (K:=K) (m:=Fin 3) i₀ (by norm_num)
    · simpa [threeTwoFrameDegree,balancedDegreeList] using
        generic_above_sl_kronecker_decomposition (K:=K) (m:=Fin 3) i₀ (by norm_num)
  | succ q =>
    obtain ⟨gs,hlen,_,hmin,hcanon⟩ := generic_nondivisible_gl_kronecker_structure
      (K:=K) (n:=Fin (3*(q+1)+2)) (m:=Fin 3) (q+1) (by omega)
      (by simp only [Fintype.card_fin]; omega) (by simp only [Fintype.card_fin]; omega)
    have hlen2 : gs.length=2 := by
      simp only [Fintype.card_fin] at hlen
      rw [show 3*(q+1)+2-(q+1)*3=2 by omega,
        show (q+1+1)*3-(3*(q+1)+2)=1 by omega] at hlen
      simpa using hlen
    exact generic_three_two_sl_uniform_of_pure_gl (q+1) i₀ gs hlen2 hcanon hmin

theorem generic_three_two_sl_hilbert (q d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (3*q+2)) (Fin 3))
      (genericAffineRows K (Fin (3*q+2)) (Fin 3)) d=3*(d+1-threeTwoFrameDegree q) := by
  rw [slHilbert_eq_matrix_kernel _ _ (0 : Fin (3*q+2)),
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp (generic_three_two_sl_minimal_and_kronecker q 0).1]
  simp <;> omega

end FD56
