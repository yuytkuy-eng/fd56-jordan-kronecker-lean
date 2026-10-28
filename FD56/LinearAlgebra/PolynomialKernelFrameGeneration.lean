/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ExactKernelBasis

/-! An independent polynomial frame generating the full kernel is a kernel
basis. Saturation then preserves its independence at every evaluation point. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a n r : Type*} [Field K] [Fintype n] [Fintype r]
  [DecidableEq n] [DecidableEq r]

theorem polynomial_kernel_frame_basis
    (A : Matrix a n K[X]) (Z : Matrix n r K[X])
    (hZ : Function.Injective Z.mulVec)
    (hgen : LinearMap.range (Matrix.toLin' Z)=LinearMap.ker (Matrix.toLin' A)) :
    ∃ B : Basis r K[X] (LinearMap.ker (Matrix.toLin' A)),
      polynomialKernelBasisMatrix A B=Z := by
  obtain ⟨B,hB⟩ := kernel_basis_of_unique_coordinates A Z (by
    intro x
    constructor
    · intro hx
      have hmem : x ∈ LinearMap.range (Matrix.toLin' Z) := by
        rw [hgen]
        exact hx
      obtain ⟨v,hv⟩ := hmem
      refine ⟨v,hv.symm,?_⟩
      intro w hw
      exact hZ (hw.symm.trans hv.symm)
    · rintro ⟨v,hv,_⟩
      change x ∈ LinearMap.ker (Matrix.toLin' A)
      rw [← hgen]
      exact ⟨v,hv.symm⟩)
  exact ⟨B,funext (fun i => funext (fun j => hB i j))⟩

theorem polynomial_kernel_frame_pointwise_injective
    (A : Matrix a n K[X]) (Z : Matrix n r K[X])
    (hZ : Function.Injective Z.mulVec)
    (hgen : LinearMap.range (Matrix.toLin' Z)=LinearMap.ker (Matrix.toLin' A))
    (x : K) : Function.Injective (Z.map (Polynomial.evalRingHom x)).mulVec := by
  obtain ⟨B,hB⟩ := polynomial_kernel_frame_basis A Z hZ hgen
  rw [← hB]
  exact polynomialKernelBasisMatrix_pointwise_injective A B x

end FD56
