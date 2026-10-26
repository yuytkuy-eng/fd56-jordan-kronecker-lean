/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedSLKronecker
import FD56.Hilbert.GenericMiddle
import FD56.Hilbert.GenericMiddleSLHigh
import FD56.Hilbert.EventualHilbertBudget

/-! The generic middle SL degree list exhausts the ambient dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_middle_sl_dimension_budget (i₀ : n)
    (hmn : Fintype.card m < Fintype.card n) (hnm : Fintype.card n < 2*Fintype.card m)
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    Fintype.card (SLChartInput n m i₀) = (xs.map (fun e => 2*e+1)).sum := by
  let gs := degreeConvolution
    (balancedDegreeList (Fintype.card m) (Fintype.card n-Fintype.card m))
    (balancedDegreeList (Fintype.card m+2*(Fintype.card n-Fintype.card m))
      (Fintype.card m-(Fintype.card n-Fintype.card m)))
  let N := Fintype.card m / (Fintype.card n-Fintype.card m) +
    (Fintype.card m+2*(Fintype.card n-Fintype.card m)) /
      (Fintype.card m-(Fintype.card n-Fintype.card m)) + 2
  have hSL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hmin
  have hGL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (generic_middle_gl_minimal_degrees (K := K) hmn hnm)
  have hhigh (d : ℕ) (hd : N ≤ d) : (xs.map (fun e => d+1-e)).sum =
      (gs.map (fun e => d+1-e)).sum + (d+2) := by
    have he := generic_middle_slHilbert_high (K := K) i₀ hmn hnm d hd
    rw [slHilbert_eq_matrix_kernel _ _ i₀, hSL, hGL] at he
    exact he
  have hb := eventual_hilbert_scalar_block_dimension gs xs N hhigh
  have hdim : (gs.map (fun e => 2*e+1)).sum = Fintype.card (SLInput n m) := by
    rw [show gs = degreeConvolution
      (balancedDegreeList (Fintype.card m) (Fintype.card n-Fintype.card m))
      (balancedDegreeList (Fintype.card m+2*(Fintype.card n-Fintype.card m))
        (Fintype.card m-(Fintype.card n-Fintype.card m))) from rfl,
      middle_gl_dimension_budget _ _ hmn hnm]
    simp only [SLInput, Fintype.card_sum, Fintype.card_prod]
    ring
  rw [hdim] at hb
  rw [slChartInput_card]
  omega

theorem generic_middle_sl_kronecker_of_minimal_degrees (i₀ : n)
    (hmn : Fintype.card m < Fintype.card n) (hnm : Fintype.card n < 2*Fintype.card m)
    (xs : List ℕ) (hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs :=
  slKirillovMatrix_kronecker _ _ i₀ xs
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hmin
    (generic_middle_sl_dimension_budget i₀ hmn hnm xs hmin)

theorem generic_middle_sl_exists_kronecker_decomposition (i₀ : n)
    (hmn : Fintype.card m < Fintype.card n) (hnm : Fintype.card n < 2*Fintype.card m) :
    ∃ xs : List ℕ, HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs := by
  obtain ⟨r, B, e, hZ, hlead, _, _⟩ := polynomial_kernel_has_minimal_basis
    (slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
  have hm : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) (List.ofFn e) :=
    ⟨r, B, e, hZ, hlead, List.Perm.refl _⟩
  exact ⟨List.ofFn e, hm, generic_middle_sl_kronecker_of_minimal_degrees i₀ hmn hnm _ hm⟩

end FD56
