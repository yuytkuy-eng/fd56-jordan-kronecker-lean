/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelKernelDegrees
import FD56.LinearAlgebra.ExactKernelBasis
import FD56.Hilbert.MinimalProfile

/-! The inverse Hankel construction realizes the prescribed minimal kernel degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {b c : ℕ}

theorem hankelFrame_minimal_degrees (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) :
    HasMinimalKernelDegrees (hankelFrame h g a B) (List.ofFn h) := by
  obtain ⟨Bv,hBv⟩ := kernel_basis_of_unique_coordinates (hankelFrame h g a B)
    (hankelKernelMatrix h g a B hg) (hankelKernelMatrix_exact h g a B hBH hHB hh hg)
  have he : polynomialKernelBasisMatrix (hankelFrame h g a B) Bv =
      hankelKernelMatrix h g a B hg := funext fun i => funext fun j => hBv i j
  refine ⟨b,Bv,h,?_,?_,List.Perm.refl _⟩
  · rw [he]
    exact hankelKernelMatrix_degree h g a B hh hg
  · rw [he]
    exact hankelKernelMatrix_leading_injective h g a B hh hg

theorem hankelFrame_kernel_hilbert (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (hankelFrame h g a B) d) =
      ∑ j, (d+1-h j) := by
  have he := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (hankelFrame_minimal_degrees h g a B hBH hHB hh hg) d
  simpa only [List.map_ofFn,List.sum_ofFn,Function.comp_apply] using he

end FD56
