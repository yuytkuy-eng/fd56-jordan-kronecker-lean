/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTripleBalancedSeeds
import FD56.Hilbert.SixOutputTripleSeedCriterion
import FD56.Hilbert.GenericSixOutputTripleSLDivisibleTangent
import FD56.Arithmetic.SixOutputTripleSeedWeights

/-! Complete characteristic-zero SL Kronecker classification for the
six-output middle remainder at every positive depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_middle_sl_classification
    (q : ℕ) (hq : 0<q) (i₀ : Fin (6*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
      (genericAffineRows K (Fin (6*q+3)) (Fin 6)) i₀)
      (balancedDegreeList (10*(interiorFullWeight 3 3 q-1)-4*interiorFullWeight 3 3 q) 10) := by
  obtain ⟨s,hs,t,hweight⟩ := six_output_triple_tangent_seed_degree q hq
  by_cases hs5 : s=5
  · subst s
    exact generic_six_output_triple_sl_divisible_tangent_classification
      q (t+1) hq (by omega) (by omega) i₀
  · have hs' : s∈([1,4] : List ℕ) := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs ⊢
      omega
    obtain ⟨G,hG,hdG,hzero,hcritical⟩ := exists_six_output_triple_balanced_seed (K:=K) s hs'
    have hpos : 0<12*s/10 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs'
      omega
    exact generic_six_output_triple_sl_classification_of_seed
      q s t hq hweight i₀ G hG hdG hpos hzero hcritical

end FD56
