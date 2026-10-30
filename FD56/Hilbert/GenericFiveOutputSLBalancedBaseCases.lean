/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericFiveOutputSLDivisibleTangent
import FD56.Hilbert.GenericFiveOutputCorankTwoSLDivisibleTangent
import FD56.Hilbert.MixedOneTwoSLClassification
import FD56.Hilbert.MixedOneThreeSLClassification

/-! Balanced-list forms of the divisible five-output classifications and
the two first-depth interior cases. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

private theorem balanced_divisible (h : ℕ) (hh : 0<h) :
    balancedDegreeList (7*(14*h-1)-2*(14*h)) 7=List.replicate 7 (10*h-1) := by
  have he : 7*(14*h-1)-2*(14*h)=7*(10*h-1) := by omega
  rw [he]
  simp [balancedDegreeList]

variable {K : Type*} [Field K] [CharZero K]

theorem generic_five_output_sl_divisible_balanced_classification
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : twoColumnInteriorWeight 3 q=14*h) (i₀ : Fin (5*q+2)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+2)) (Fin 5))
      (genericAffineRows K (Fin (5*q+2)) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 q-1)-2*twoColumnInteriorWeight 3 q) 7) := by
  rw [hweight,balanced_divisible h hh]
  exact generic_five_output_sl_divisible_tangent_classification q h hq hh hweight i₀

theorem generic_five_output_corank_two_sl_divisible_balanced_classification
    (q h : ℕ) (hq : 0<q) (hh : 0<h)
    (hweight : interiorFullWeight 3 2 q=14*h) (i₀ : Fin (5*q+3)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin (5*q+3)) (Fin 5))
      (genericAffineRows K (Fin (5*q+3)) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 q-1)-2*interiorFullWeight 3 2 q) 7) := by
  rw [hweight,balanced_divisible h hh]
  exact generic_five_output_corank_two_sl_divisible_tangent_classification q h hq hh hweight i₀

private theorem canonical_of_minimal {n : ℕ} (i₀ : Fin n) (xs ys : List ℕ)
    (hxs : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin 5))
      (genericAffineRows K (Fin n) (Fin 5)) i₀) xs)
    (hcanon : HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin n) (Fin 5))
      (genericAffineRows K (Fin n) (Fin 5)) i₀) xs)
    (hys : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin n) (Fin 5))
      (genericAffineRows K (Fin n) (Fin 5)) i₀) ys) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin n) (Fin 5))
      (genericAffineRows K (Fin n) (Fin 5)) i₀) ys := by
  have hp : xs.Perm ys := by
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_nat,listHilbert_nat]
    exact_mod_cast ((hasMinimalKernelDegrees_iff_hilbert _ xs).mp hxs d).symm.trans
      ((hasMinimalKernelDegrees_iff_hilbert _ ys).mp hys d)
  obtain ⟨k,e,he,T,U,hTU,hUT,hcanonical⟩ := hcanon
  exact ⟨k,e,he.trans hp,T,U,hTU,hUT,hcanonical⟩

theorem generic_five_output_sl_first_depth_classification (i₀ : Fin 7) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 7) (Fin 5)) (genericAffineRows K (Fin 7) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 1-1)-2*twoColumnInteriorWeight 3 1) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 7) (Fin 5)) (genericAffineRows K (Fin 7) (Fin 5)) i₀)
      (balancedDegreeList (7*(twoColumnInteriorWeight 3 1-1)-2*twoColumnInteriorWeight 3 1) 7) := by
  have hmin := generic_third_near_double_sl_minimal_degrees_all (K:=K) 7 5
    (by decide) (by decide) i₀
  change HasMinimalKernelDegrees _ (balancedDegreeList 38 7) ∧
    HasKroneckerDecomposition _ (balancedDegreeList 38 7)
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin 7) (m:=Fin 5) 1 (by decide) i₀ (by decide) (by decide)
  exact canonical_of_minimal i₀ xs _ hxs hcanon hmin

theorem generic_five_output_corank_two_sl_first_depth_classification (i₀ : Fin 8) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin 8) (Fin 5)) (genericAffineRows K (Fin 8) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 1-1)-2*interiorFullWeight 3 2 1) 7) ∧
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K (Fin 8) (Fin 5)) (genericAffineRows K (Fin 8) (Fin 5)) i₀)
      (balancedDegreeList (7*(interiorFullWeight 3 2 1-1)-2*interiorFullWeight 3 2 1) 7) := by
  have hmin := generic_second_near_double_sl_minimal_degrees
    (K:=K) (n:=Fin 8) (m:=Fin 5) (by decide) (by decide) i₀
  change HasMinimalKernelDegrees _ (balancedDegreeList 48 7) ∧
    HasKroneckerDecomposition _ (balancedDegreeList 48 7)
  refine ⟨hmin,?_⟩
  obtain ⟨xs,_,_,hxs,hcanon⟩ := generic_nondivisible_sl_kronecker_structure
    (K:=K) (n:=Fin 8) (m:=Fin 5) 1 (by decide) i₀ (by decide) (by decide)
  exact canonical_of_minimal i₀ xs _ hxs hcanon hmin

end FD56
