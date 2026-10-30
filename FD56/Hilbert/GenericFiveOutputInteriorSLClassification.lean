/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputBalancedSeeds
import FD56.Hilbert.FiveOutputIteratedSeedCriterion
import FD56.Hilbert.GenericFiveOutputSLBalancedBaseCases
import FD56.Arithmetic.FiveOutputSeedWeights

/-! Complete balanced SL Kronecker decompositions for the two interior
remainders n=5q+2 and n=5q+3, at every positive depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

private theorem remainder_two_weight_twice (q : ℕ) :
    2*twoColumnInteriorWeight 3 q=5*q^2+9*q+4 := by
  obtain ⟨h,hh⟩ := Nat.even_mul_succ_self q
  have hn : 5*q*(q+1)+4*(q+1)=2*(5*h+2*(q+1)) := by nlinarith
  unfold twoColumnInteriorWeight
  norm_num only [Nat.reduceAdd]
  have hd : (5*q*(q+1)+4*(q+1))/2=5*h+2*(q+1) := by omega
  rw [hd]
  nlinarith

variable {K : Type*} [Field K] [CharZero K]

theorem generic_five_output_sl_classification_of_depth_ge_two
    (q : ℕ) (hq : 2≤q) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) := by
  obtain ⟨s,hs,t,hweight⟩ := five_output_tangent_seed_weight q
    (twoColumnInteriorWeight 3 q) hq (remainder_two_weight_twice q)
  by_cases hs14 : s=14
  · subst s
    exact generic_five_output_sl_divisible_balanced_classification q (t+1)
      (by omega) (by omega) (by omega) i₀
  · have hs' : s ∈ ([16,17,18,21,23,24,25] : List ℕ) :=
      (List.mem_cons.mp hs).resolve_left hs14
    obtain ⟨a,b,u,v,hab,hsum,hu,hv,hdu,hdv,hzero,hcritical⟩ :=
      exists_five_output_balanced_seed (K:=K) s hs'
    have hlarge : 16≤s := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs'
      omega
    subst s
    apply generic_five_output_sl_classification_of_iterated_seed q a b t (by omega) hab
      hweight i₀ u v hu hv hdu hdv (by omega)
    · exact hzero
    · exact hcritical

theorem generic_five_output_corank_two_sl_classification_of_depth_ge_two
    (q : ℕ) (hq : 2≤q) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) := by
  obtain ⟨s,hs,t,hweight⟩ := five_output_corank_two_tangent_seed_weight q
    (interiorFullWeight 3 2 q) hq (five_output_corank_two_weight_twice q)
  by_cases hs14 : s=14
  · subst s
    exact generic_five_output_corank_two_sl_divisible_balanced_classification q (t+1)
      (by omega) (by omega) (by omega) i₀
  · have hs' : s ∈ ([16,17,18,21,23,24,25] : List ℕ) :=
      (List.mem_cons.mp hs).resolve_left hs14
    obtain ⟨a,b,u,v,hab,hsum,hu,hv,hdu,hdv,hzero,hcritical⟩ :=
      exists_five_output_balanced_seed (K:=K) s hs'
    have hlarge : 16≤s := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hs'
      omega
    subst s
    apply generic_five_output_corank_two_sl_classification_of_iterated_seed q a b t (by omega) hab
      hweight i₀ u v hu hv hdu hdv (by omega)
    · exact hzero
    · exact hcritical

theorem generic_five_output_sl_interior_classification
    (q : ℕ) (hq : 0<q) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) := by
  by_cases hq1 : q=1
  · subst q
    exact generic_five_output_sl_first_depth_classification i₀
  · exact generic_five_output_sl_classification_of_depth_ge_two q (by omega) i₀

theorem generic_five_output_corank_two_sl_interior_classification
    (q : ℕ) (hq : 0<q) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) := by
  by_cases hq1 : q=1
  · subst q
    exact generic_five_output_corank_two_sl_first_depth_classification i₀
  · exact generic_five_output_corank_two_sl_classification_of_depth_ge_two q (by omega) i₀

end FD56
