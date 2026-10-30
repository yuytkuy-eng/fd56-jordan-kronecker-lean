/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputBalancedSeeds
import FD56.Hilbert.SixOutputShortSeedCriterion
import FD56.Hilbert.GenericSixOutputSLDivisibleTangent
import FD56.Arithmetic.SixOutputSeedWeights

/-! Complete characteristic-zero SL Kronecker classifications for the
six-output remainders two and four at every positive depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_sl_two_column_classification
    (q : ℕ) (hq : 0<q) (i₀ : Fin (6*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*((twoColumnInteriorWeight 4 q)-1)-3*(twoColumnInteriorWeight 4 q)) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+2)) (Fin 6))
      (genericAffineRows K (Fin (6*q+2)) (Fin 6)) i₀)
      (balancedDegreeList (9*((twoColumnInteriorWeight 4 q)-1)-3*(twoColumnInteriorWeight 4 q)) 9) := by
  obtain ⟨s,hs,t,hweight⟩ := six_output_tangent_seed_weight q (twoColumnInteriorWeight 4 q) hq (six_output_two_column_weight q)
  by_cases hs6 : s=6
  · subst s
    exact generic_six_output_sl_divisible_tangent_classification
      q (t+1) hq (by omega) (by omega) i₀
  · have hs' : s ∈ ([8,10] : List ℕ) := (List.mem_cons.mp hs).resolve_left hs6
    obtain ⟨a,b,u,v,hab,hsum,hu,hv,hdu,hdv,hzero,hcritical⟩ :=
      exists_six_output_balanced_seed (K:=K) s hs'
    subst s
    have hlarge : 8≤a+b := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs'
      omega
    exact generic_six_output_sl_classification_of_short_seed q a b t hq hab
      hweight i₀ u v hu hv hdu hdv (by omega) hzero hcritical

theorem generic_six_output_corank_two_sl_two_column_classification
    (q : ℕ) (hq : 0<q) (i₀ : Fin (6*q+4)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*((interiorFullWeight 4 2 q)-1)-3*(interiorFullWeight 4 2 q)) 9) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (6*q+4)) (Fin 6))
      (genericAffineRows K (Fin (6*q+4)) (Fin 6)) i₀)
      (balancedDegreeList (9*((interiorFullWeight 4 2 q)-1)-3*(interiorFullWeight 4 2 q)) 9) := by
  obtain ⟨s,hs,t,hweight⟩ := six_output_corank_two_tangent_seed_weight q (interiorFullWeight 4 2 q) hq (six_output_corank_two_weight q)
  by_cases hs6 : s=6
  · subst s
    exact generic_six_output_corank_two_sl_divisible_tangent_classification
      q (t+1) hq (by omega) (by omega) i₀
  · have hs' : s ∈ ([8,10] : List ℕ) := (List.mem_cons.mp hs).resolve_left hs6
    obtain ⟨a,b,u,v,hab,hsum,hu,hv,hdu,hdv,hzero,hcritical⟩ :=
      exists_six_output_balanced_seed (K:=K) s hs'
    subst s
    have hlarge : 8≤a+b := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs'
      omega
    exact generic_six_output_corank_two_sl_classification_of_short_seed q a b t hq hab
      hweight i₀ u v hu hv hdu hdv (by omega) hzero hcritical

end FD56
