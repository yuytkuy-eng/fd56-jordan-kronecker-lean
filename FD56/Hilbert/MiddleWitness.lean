/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.RectangularLift
import FD56.Hilbert.PrescribedDegrees
import FD56.LinearAlgebra.MonomialLift

/-! Affine middle factors realize arbitrary polynomial auxiliary matrices
for adjacent rectangular block lengths, including balanced kernel witnesses. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r]

theorem rectangularBlockPencil_affine_middle_lift (e : r → ℕ)
    (he : ∀ i j, e i ≤ e j + 1) (G : Matrix (Σ i, Fin (e i)) r K[X])
    (hG : ∀ x j, (G x j).natDegree ≤ e j + 2) :
    ∃ M : Matrix (Σ i, Fin (e i + 1)) (Σ i, Fin (e i + 1)) K[X],
      DegreeBound M 1 ∧ rectangularBlockPencil e * M * blockMonomialKernel e = G := by
  obtain ⟨W, hW, hPW⟩ := rectangularBlockPencil_balanced_lift e he G hG
  obtain ⟨M, hM, hMV⟩ := exists_affine_monomial_lift e W hW
  refine ⟨M, hM, ?_⟩
  rw [Matrix.mul_assoc, hMV, hPW]

theorem exists_affine_middle_balanced_kernel (e : r → ℕ)
    (he : ∀ i j, e i ≤ e j + 1) (hr : Fintype.card r < ∑ i, e i) :
    ∃ M : Matrix (Σ i, Fin (e i + 1)) (Σ i, Fin (e i + 1)) K[X],
      DegreeBound M 1 ∧
      ∀ d, Module.finrank K (polynomialKernelAtDegree
        (rectangularBlockPencil e * M * blockMonomialKernel e).transpose d) =
        ((∑ i, e i) - Fintype.card r) * (d + 1) - ∑ j, (e j + 2) := by
  have hcard : Fintype.card r < Fintype.card (Σ i, Fin (e i)) := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using hr
  obtain ⟨G, hG, hH⟩ := exists_prescribed_column_matrix_balanced_kernel
    (K := K) (fun j => e j + 2) hcard
  obtain ⟨M, hM, hPMG⟩ := rectangularBlockPencil_affine_middle_lift e he G hG
  refine ⟨M, hM, ?_⟩
  intro d
  rw [hPMG]
  simpa only [Fintype.card_sigma, Fintype.card_fin] using hH d

theorem blockMonomialKernel_mulVec (e : r → ℕ) (c : r → K[X])
    (j : r) (k : Fin (e j + 1)) :
    (blockMonomialKernel e *ᵥ c) ⟨j, k⟩ = (-Polynomial.X) ^ k.val * c j := by
  simp [Matrix.mulVec, dotProduct, blockMonomialKernel]

theorem rectangularBlockPencil_mul_blockMonomialKernel (e : r → ℕ) :
    rectangularBlockPencil (K := K) e * blockMonomialKernel (K := K) e = 0 := by
  funext ⟨i, x⟩ j
  change (rectangularBlockPencil e *ᵥ (fun y => blockMonomialKernel e y j)) ⟨i, x⟩ = 0
  rw [rectangularBlockPencil, blockDiagonal_mulVec]
  by_cases hij : i = j
  · subst j
    have h := (bidiagonalPencil_kernel_iff (e i)
      (fun k => (-Polynomial.X : K[X]) ^ k.val)).mpr (by intro k; simp)
    simpa only [blockMonomialKernel, if_pos rfl] using congrFun h x
  · simp [blockMonomialKernel, hij, Matrix.mulVec, dotProduct]

def rectangularBlockKernelEquiv (e : r → ℕ) :
    LinearMap.ker (Matrix.toLin' (rectangularBlockPencil (K := K) e)) ≃ₗ[K[X]]
      (r → K[X]) where
  toFun v j := v.val ⟨j, 0⟩
  invFun c := ⟨blockMonomialKernel e *ᵥ c, by
    change rectangularBlockPencil e *ᵥ (blockMonomialKernel e *ᵥ c) = 0
    rw [Matrix.mulVec_mulVec, rectangularBlockPencil_mul_blockMonomialKernel]
    simp⟩
  left_inv v := by
    apply Subtype.ext
    funext ⟨j, k⟩
    change (blockMonomialKernel e *ᵥ (fun i => v.val ⟨i, 0⟩)) ⟨j, k⟩ = v.val ⟨j, k⟩
    rw [blockMonomialKernel_mulVec]
    have hj : bidiagonalPencil (e j) *ᵥ (fun k => v.val ⟨j, k⟩) = 0 :=
      (blockDiagonal_kernel_iff (fun j => bidiagonalPencil (e j)) v.val).mp v.property j
    exact (bidiagonalPencil_kernel_coordinates (e j) _ hj k).symm
  right_inv c := by
    funext j
    simp [blockMonomialKernel_mulVec]
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def rectangularBlockKernelBasis (e : r → ℕ) :
    Basis r K[X] (LinearMap.ker (Matrix.toLin' (rectangularBlockPencil (K := K) e))) :=
  (Pi.basisFun K[X] r).map (rectangularBlockKernelEquiv e).symm

theorem polynomialKernelBasisMatrix_rectangularBlock (e : r → ℕ) :
    polynomialKernelBasisMatrix (rectangularBlockPencil (K := K) e)
      (rectangularBlockKernelBasis e) = blockMonomialKernel e := by
  funext ⟨i, k⟩ j
  change (blockMonomialKernel e *ᵥ ((Pi.basisFun K[X] r) j)) ⟨i, k⟩ =
    blockMonomialKernel e ⟨i, k⟩ j
  rw [blockMonomialKernel_mulVec]
  simp [blockMonomialKernel, Pi.basisFun_apply, Pi.single_apply, eq_comm]

end FD56
