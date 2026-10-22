/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.Tall
import FD56.LinearAlgebra.CoefficientMatrix

/-! A surjective coefficient matrix determines the bounded SL radical
through the scalar subspace of the right multiplication map. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K l n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [Fintype n] [DecidableEq n] [DecidableEq m] in
theorem boundedRightProduct_surjective_of_coefficient (P : Matrix m n K[X])
    (hP : DegreeBound P 1) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P.transpose d).mulVec) :
    Function.Surjective (boundedRightProduct (l := l) P hP d) := by
  intro W
  have hr (i : l) : ∃ v : m → K[X], (∀ j, (v j).natDegree ≤ d) ∧
      P.transpose *ᵥ v = fun k => (W i k).val := by
    apply polynomial_preimage_of_coefficient_surjective P.transpose d
      (fun i j => hP j i) hs
    exact fun k => boundedPoly_degree (d + 1) (W i k)
  choose U hU hUP using hr
  refine ⟨fun i j => boundedPolyOf (U i j) (hU i j), ?_⟩
  funext i k
  apply Subtype.ext
  have he := congrFun (hUP i) k
  simpa [boundedRightProduct, boundedPolyOf, entries, Matrix.mulVec,
    dotProduct, Matrix.mul_apply, mul_comm] using he

omit [DecidableEq n] [DecidableEq m] in
theorem boundedRightProduct_kernel_finrank_of_coefficient [Fintype l]
    (P : Matrix m n K[X]) (hP : DegreeBound P 1) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P.transpose d).mulVec) :
    Module.finrank K (LinearMap.ker (boundedRightProduct (l := l) P hP d)) =
      Fintype.card l * Fintype.card m * (d + 1) -
        Fintype.card l * Fintype.card n * (d + 2) := by
  have hd := (boundedRightProduct (l := l) P hP d).finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (boundedRightProduct_surjective_of_coefficient P hP d hs),
    finrank_top, boundedMatrix_finrank, boundedMatrix_finrank] at hd
  norm_num only [Nat.add_assoc] at hd
  exact Nat.eq_sub_of_add_eq (Nat.add_comm _ _ |>.trans hd)

theorem slHilbert_of_coefficient_surjective (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hP : DegreeBound P 1)
    (R : Matrix n m K[X]) (hR : R * P = 1) (i₀ : n) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P.transpose d).mulVec) :
    slHilbert M P d =
      (Fintype.card n * Fintype.card m * (d + 1) -
        Fintype.card n * Fintype.card n * (d + 2)) + (d + 2) := by
  unfold slHilbert
  rw [(tallSLKernelEquiv M P hP R hR i₀ d).finrank_eq,
    surjective_comap_finrank _ (boundedRightProduct_surjective_of_coefficient P hP d hs),
    boundedRightProduct_kernel_finrank_of_coefficient P hP d hs,
    boundedScalarSpace_finrank i₀]

theorem slHilbert_of_transpose_coefficient_surjective (M : Matrix n n K[X])
    (P : Matrix m n K[X]) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ)
    (hs : Function.Surjective (polynomialCoefficientMatrix P.transpose d).mulVec) :
    slHilbert M P d =
      (Fintype.card n * Fintype.card m * (d + 1) -
        Fintype.card n * Fintype.card n * (d + 2)) + (d + 2) := by
  obtain ⟨Q, _, hQ⟩ := polynomial_right_inverse_of_coefficient_surjective
    P.transpose d (fun i j => hP j i) hs
  have hR : (show Matrix n n K[X] from Q.transpose * P) = 1 := by
    have hh := congrArg Matrix.transpose hQ
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.transpose_one] using hh
  exact slHilbert_of_coefficient_surjective M P hP Q.transpose hR i₀ d hs

end FD56
