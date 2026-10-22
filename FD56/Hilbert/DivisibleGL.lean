/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericPencil
import FD56.Hilbert.GLMatrix
import FD56.Hilbert.KernelDimension

/-! The divisible GL family has no nonzero polynomial kernel vectors.
The canonical index type has (q + 1) times as many columns as rows. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem polynomial_kernel_eq_bot_of_map_nullity_zero
    {K F a b : Type*} [Field K] [Field F] [Fintype b] [DecidableEq b]
    (A : Matrix a b K[X]) (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (hzero : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = 0) (d : ℕ) :
    polynomialKernelAtDegree A d = ⊥ := by
  have hi : Function.Injective (A.map φ).mulVec :=
    LinearMap.ker_eq_bot.mp (Submodule.finrank_eq_zero.mp hzero)
  have hiA := matrix_mulVec_injective_of_map φ hφ A hi
  apply (Submodule.eq_bot_iff _).mpr
  intro v hv
  have hz := hiA (hv.trans (Matrix.mulVec_zero A).symm)
  funext j
  exact Subtype.ext (congrFun hz j)

theorem polynomial_kernel_hilbert_of_map_nullity_zero
    {K F a b : Type*} [Field K] [Field F] [Fintype b] [DecidableEq b]
    (A : Matrix a b K[X]) (φ : K[X] →+* F) (hφ : Function.Injective φ)
    (hzero : Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) = 0) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree A d) = 0 := by
  rw [polynomial_kernel_eq_bot_of_map_nullity_zero A φ hφ hzero d, finrank_bot]

theorem generic_divisible_gl_kernel_eq_bot {K : Type*} {s : Type}
    [Field K] [Fintype s] [Nonempty s] [DecidableEq s] (q d : ℕ) :
    polynomialKernelAtDegree (glEquationMatrix
      (genericAffineSquare K (blockIndex (Empty ⊕ s) Empty (q + 1)) (Empty ⊕ s))
      (genericAffineRows K (blockIndex (Empty ⊕ s) Empty (q + 1)) (Empty ⊕ s))) d = ⊥ := by
  let N := blockIndex (Empty ⊕ s) Empty (q + 1)
  let M := genericAffineSquare K N (Empty ⊕ s)
  let P := genericAffineRows K N (Empty ⊕ s)
  let F := GenericPencilField K N (Empty ⊕ s)
  let φ := algebraMap ((AffineCoefficientField K (MatrixParameters N (Empty ⊕ s)))[X]) F
  have hz : Module.finrank F (LinearMap.ker (Matrix.toLin' ((glEquationMatrix M P).map φ))) = 0 := by
    rw [glEquationMatrix_map, glEquationMatrix_field_finrank]
    have hh := (generic_pencil_radical_dimensions (K := K) (r := Empty) (s := s) q).1
    simpa only [Fintype.card_empty, zero_mul] using hh
  exact polynomial_kernel_eq_bot_of_map_nullity_zero _ φ (IsFractionRing.injective _ _) hz d

theorem generic_divisible_gl_kernel_hilbert {K : Type*} {s : Type}
    [Field K] [Fintype s] [Nonempty s] [DecidableEq s] (q d : ℕ) :
    Module.finrank (AffineCoefficientField K
      (MatrixParameters (blockIndex (Empty ⊕ s) Empty (q + 1)) (Empty ⊕ s)))
      (polynomialKernelAtDegree (glEquationMatrix
        (genericAffineSquare K (blockIndex (Empty ⊕ s) Empty (q + 1)) (Empty ⊕ s))
        (genericAffineRows K (blockIndex (Empty ⊕ s) Empty (q + 1)) (Empty ⊕ s))) d) = 0 := by
  rw [generic_divisible_gl_kernel_eq_bot q d, finrank_bot]

end FD56
