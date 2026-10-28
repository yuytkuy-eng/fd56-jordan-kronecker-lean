/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerSLHilbert
import FD56.Hilbert.KroneckerDimension
import FD56.Hilbert.MixedSLKronecker
import FD56.Hilbert.EventualHilbertBudget

/-! A pure generic GL pencil yields a pure SL pencil, with one additional
Kronecker block and total minimal degree smaller by one. Individual SL
minimal degrees are not determined by this statement. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem generic_sl_profile_of_gl_kronecker
    (hm : 0<Fintype.card m) (i₀ : n) (gs : List ℕ)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (hminGL : HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (xs : List ℕ) (hminSL : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    xs.length=gs.length+1 ∧ xs.sum+1=gs.sum := by
  have hSL := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hminSL
  have hGLh := (hasMinimalKernelDegrees_iff_hilbert _ _).mp hminGL
  apply eventual_hilbert_scalar_profile gs xs gs.sum
  intro d hd
  have he := generic_slHilbert_high_of_gl_kronecker hm i₀ gs hGL d (by
    intro e he
    exact (List.le_sum_of_mem he).trans (by omega))
  rw [slHilbert_eq_matrix_kernel _ _ i₀,hSL,hGLh] at he
  exact he

theorem generic_sl_kronecker_of_gl_kronecker
    (hm : 0<Fintype.card m) (i₀ : n) (gs : List ℕ)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (hminGL : HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (xs : List ℕ) (hminSL : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    HasKroneckerDecomposition (slKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs := by
  obtain ⟨hl,hs⟩ := generic_sl_profile_of_gl_kronecker hm i₀ gs hGL hminGL xs hminSL
  have hc := kronecker_decomposition_dimension _ _ hGL
  rw [nat_list_affine_sum] at hc
  apply slKirillovMatrix_kronecker _ _ i₀ xs
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hminSL
  rw [slChartInput_card,nat_list_affine_sum]
  simp only [one_mul] at hc ⊢
  omega

theorem generic_sl_exists_kronecker_of_gl_kronecker
    (hm : 0<Fintype.card m) (i₀ : n) (gs : List ℕ)
    (hGL : HasKroneckerDecomposition (glKirillovMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs)
    (hminGL : HasMinimalKernelDegrees (glEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m)) gs) :
    ∃ xs : List ℕ, xs.length=gs.length+1 ∧ xs.sum+1=gs.sum ∧
      HasMinimalKernelDegrees (slEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs ∧
      HasKroneckerDecomposition (slKirillovMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs := by
  obtain ⟨r,B,e,hZ,hlead,_,_⟩ := polynomial_kernel_has_minimal_basis
    (slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀)
  have hmin : HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) i₀) (List.ofFn e) :=
    ⟨r,B,e,hZ,hlead,List.Perm.refl _⟩
  obtain ⟨hl,hs⟩ := generic_sl_profile_of_gl_kronecker hm i₀ gs hGL hminGL _ hmin
  exact ⟨List.ofFn e,hl,hs,hmin,
    generic_sl_kronecker_of_gl_kronecker hm i₀ gs hGL hminGL _ hmin⟩

end FD56
