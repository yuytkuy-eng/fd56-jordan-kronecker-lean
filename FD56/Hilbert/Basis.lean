/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.KernelBasis
import FD56.Hilbert.KernelDimension

/-! A polynomial kernel basis with independent leading columns determines
the entire degree filtration, over any field. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b k : Type*} [Field K] [Fintype b] [DecidableEq b] [Fintype k]

theorem kernelFromBasisCoordinates_bijective (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (e : k → ℕ) (d : ℕ)
    (hZ : ∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j)
    (hlead : Function.Injective
      (Matrix.mulVec (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (e j)))) :
    Function.Bijective (kernelFromCoordinates A (polynomialKernelBasisMatrix A B) e d
      (polynomialKernelBasisMatrix_mul A B) hZ) := by
  constructor
  · intro c c' h
    have hv : polynomialKernelBasisMatrix A B *ᵥ (fun j => (c j).val) =
        polynomialKernelBasisMatrix A B *ᵥ (fun j => (c' j).val) :=
      congrArg (fun Y : polynomialKernelAtDegree A d => fun i => (Y.val i).val) h
    rw [polynomialKernelBasisMatrix_mulVec, polynomialKernelBasisMatrix_mulVec] at hv
    have he : B.equivFun.symm (fun j => (c j).val) =
        B.equivFun.symm (fun j => (c' j).val) := Subtype.ext hv
    have hc := B.equivFun.symm.injective he
    funext j
    exact Subtype.ext (congrFun hc j)
  · intro Y
    let y : LinearMap.ker (Matrix.toLin' A) := ⟨fun i => (Y.val i).val, Y.property⟩
    let c : k → K[X] := B.equivFun y
    have hc : polynomialKernelBasisMatrix A B *ᵥ c = fun i => (Y.val i).val := by
      rw [polynomialKernelBasisMatrix_mulVec]
      exact congrArg Subtype.val (B.equivFun.symm_apply_apply y)
    have hb : ∀ j, c j = 0 ∨ (e j ≤ d ∧ (c j).natDegree ≤ d - e j) := by
      apply (polynomial_combination_degree_iff (polynomialKernelBasisMatrix A B) e c d hZ hlead).mp
      intro i
      rw [hc]
      exact boundedPoly_degree d (Y.val i)
    let c' : ∀ j, Polynomial.degreeLT K (d + 1 - e j) :=
      fun j => ⟨c j, (mem_degreeLT_shift_iff (c j) d (e j)).mpr (hb j)⟩
    refine ⟨c', ?_⟩
    apply Subtype.ext
    funext i
    apply Subtype.ext
    exact congrFun hc i

def polynomialKernelBasisDegreeEquiv (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (e : k → ℕ) (d : ℕ)
    (hZ : ∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j)
    (hlead : Function.Injective
      (Matrix.mulVec (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (e j)))) :
    polynomialKernelAtDegree A d ≃ₗ[K] ∀ j, Polynomial.degreeLT K (d + 1 - e j) :=
  (LinearEquiv.ofBijective
    (kernelFromCoordinates A (polynomialKernelBasisMatrix A B) e d
      (polynomialKernelBasisMatrix_mul A B) hZ)
    (kernelFromBasisCoordinates_bijective A B e d hZ hlead)).symm

theorem polynomial_kernel_basis_hilbert (A : Matrix a b K[X])
    (B : Basis k K[X] (LinearMap.ker (Matrix.toLin' A)))
    (e : k → ℕ) (d : ℕ)
    (hZ : ∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j)
    (hlead : Function.Injective
      (Matrix.mulVec (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (e j)))) :
    Module.finrank K (polynomialKernelAtDegree A d) = ∑ j, (d + 1 - e j) := by
  rw [(polynomialKernelBasisDegreeEquiv A B e d hZ hlead).finrank_eq]
  letI (j : k) : Module.Finite K (Polynomial.degreeLT K (d + 1 - e j)) :=
    Module.Finite.of_injective (Polynomial.degreeLTEquiv K (d + 1 - e j)).toLinearMap
      (Polynomial.degreeLTEquiv K (d + 1 - e j)).injective
  rw [Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro j _
  rw [(Polynomial.degreeLTEquiv K (d + 1 - e j)).finrank_eq]
  simp

end FD56
