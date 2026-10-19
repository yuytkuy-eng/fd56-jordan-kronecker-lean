/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BidiagonalPencil
import FD56.Hilbert.KernelDimension

/-! The exact bounded polynomial kernel of a rectangular Kronecker pencil.
Its single generating vector has degree m. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def bidiagonalKernelDegreeEquiv (m d : ℕ) :
    polynomialKernelAtDegree (bidiagonalPencil (K := K) m) d ≃ₗ[K]
      Polynomial.degreeLT K (d + 1 - m) where
  toFun v := ⟨(v.val 0).val, (mem_degreeLT_shift_iff _ d m).mpr
    ((bidiagonalPencil_degree_iff m d (fun j => (v.val j).val) v.property).mp
      (fun j => boundedPoly_degree d (v.val j)))⟩
  invFun c := by
    let v : Fin (m + 1) → K[X] := fun j => (-Polynomial.X) ^ j.val * c.val
    have hv : bidiagonalPencil m *ᵥ v = 0 := by
      apply (bidiagonalPencil_kernel_iff m v).mpr
      intro j
      simp [v]
    have hb : ∀ j, (v j).natDegree ≤ d := by
      apply (bidiagonalPencil_degree_iff m d v hv).mpr
      simpa [v] using (mem_degreeLT_shift_iff c.val d m).mp c.property
    exact ⟨fun j => boundedPolyOf (v j) (hb j), hv⟩
  left_inv v := by
    apply Subtype.ext
    funext j
    apply Subtype.ext
    exact (bidiagonalPencil_kernel_coordinates m (fun j => (v.val j).val) v.property j).symm
  right_inv c := by
    apply Subtype.ext
    change (-Polynomial.X : K[X]) ^ (0 : Fin (m + 1)).val * c.val = c.val
    simp
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

theorem bidiagonal_kernel_hilbert (m d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (bidiagonalPencil (K := K) m) d) =
      d + 1 - m := by
  rw [(bidiagonalKernelDegreeEquiv m d).finrank_eq]
  rw [(Polynomial.degreeLTEquiv K (d + 1 - m)).finrank_eq]
  simp

end FD56
