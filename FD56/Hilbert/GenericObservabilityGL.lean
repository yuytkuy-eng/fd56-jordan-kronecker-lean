/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityGLDegrees
import FD56.Hilbert.GenericObservabilityLeading

/-! Generic rank conditions for the arbitrary-depth GL degree transfer.
The polynomial right inverse and auxiliary degree profiles remain explicit inputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K n m r s : Type*} [Field K]
  [Fintype n] [Fintype m] [Fintype r] [Fintype s]
  [DecidableEq n] [DecidableEq m] [DecidableEq r] [DecidableEq s]

theorem generic_observability_gl_kernel_hilbert_of_bases
    (q : ℕ) (hsize : (q+1)*Fintype.card m ≤ Fintype.card n)
    (hsize' : Fintype.card n ≤ (q+2)*Fintype.card m)
    (Bv : Basis r (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)))))
    (Bt : Basis s (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' ((genericAffineRows K n m) *
        (genericAffineSquare K n m) ^ (q+1) * polynomialKernelBasisMatrix _ Bv).transpose)))
    (R : Matrix n (Fin (q+1) × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1) * R = 1)
    (a : r → ℕ) (b : s → ℕ)
    (hV : ∀ x i, (polynomialKernelBasisMatrix _ Bv x i).natDegree ≤ a i)
    (hT : ∀ y j, (polynomialKernelBasisMatrix _ Bt y j).natDegree ≤ b j)
    (hVL : Function.Injective (Matrix.mulVec
      (fun x i => (polynomialKernelBasisMatrix _ Bv x i).coeff (a i))))
    (hTL : Function.Injective (Matrix.mulVec
      (fun y j => (polynomialKernelBasisMatrix _ Bt y j).coeff (b j)))) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m)) d) =
      ∑ ij : r × s, (d+1-(a ij.1+b ij.2+q+1)) := by
  have hmn : Fintype.card m ≤ Fintype.card n := by
    have hq := Nat.le_mul_of_pos_left (Fintype.card m) (by omega : 0 < q+1)
    omega
  exact observability_gl_kernel_hilbert_of_bases _ _ q Bv Bt R hR
    (generic_terminal_observability_injective (q+1) hsize hsize') a b
    (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m) hV hT hVL hTL
    (generic_affine_rows_leading_surjective K m n hmn)
    (generic_observability_row_leading_injective (K := K) (q+1) hsize)
    (generic_tall_observability_leading_injective (K := K) (q+2) hsize') d

theorem generic_observability_gl_minimal_degrees
    (q : ℕ) (hsize : (q+1)*Fintype.card m ≤ Fintype.card n)
    (hsize' : Fintype.card n ≤ (q+2)*Fintype.card m)
    (R : Matrix n (Fin (q+1) × m) (AffineCoefficientField K (MatrixParameters n m))[X])
    (hR : observabilityMatrix (genericAffineSquare K n m) (genericAffineRows K n m) (q+1) * R = 1)
    (alpha beta : List ℕ)
    (hAlpha : HasMinimalKernelDegrees (observabilityMatrix
      (genericAffineSquare K n m) (genericAffineRows K n m) (q+1)) alpha)
    (hBeta : ∀ (r : ℕ) (Bv : Basis (Fin r) (AffineCoefficientField K (MatrixParameters n m))[X]
      (LinearMap.ker (Matrix.toLin' (observabilityMatrix
        (genericAffineSquare K n m) (genericAffineRows K n m) (q+1))))),
      HasMinimalKernelDegrees ((genericAffineRows K n m) * (genericAffineSquare K n m) ^ (q+1) *
        polynomialKernelBasisMatrix _ Bv).transpose beta) :
    HasMinimalKernelDegrees (glEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m))
      ((degreeConvolution alpha beta).map (fun e => e+q)) := by
  obtain ⟨r,Bv,a,hV,hVL,ha⟩ := hAlpha
  obtain ⟨s,Bt,b,hT,hTL,hb⟩ := hBeta r Bv
  apply (hasMinimalKernelDegrees_iff_hilbert _ _).mpr
  intro d
  rw [generic_observability_gl_kernel_hilbert_of_bases q hsize hsize' Bv Bt R hR
    a b hV hT hVL hTL d]
  simpa only [degreeConvolution, List.map_flatMap, List.map_map, Function.comp_def,
    show ∀ x y : ℕ, x+y+1+q = x+y+q+1 by omega] using
      sum_pairs_of_permuted_degrees a b alpha beta ha hb (fun x y => d+1-(x+y+q+1))

end FD56
