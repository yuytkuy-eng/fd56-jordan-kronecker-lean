/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialDeterminantDerivative
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.FieldTheory.Separable

/-! A simple zero of a polynomial matrix determinant has a one-dimensional kernel. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K L n : Type*} [Field K] [Field L] [Fintype n] [DecidableEq n]

theorem matrix_kernel_finrank_le_one_of_updateCol_det_ne_zero
    (A : Matrix n n K) (i : n) (w : n → K) (hdet : (A.updateCol i w).det ≠ 0) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' A)) ≤ 1 := by
  let f : LinearMap.ker (Matrix.toLin' A) →ₗ[K] K :=
    (LinearMap.proj i).comp (LinearMap.ker (Matrix.toLin' A)).subtype
  have hinj : Function.Injective f := by
    apply (injective_iff_map_eq_zero f).mpr
    intro v hv
    have hcoord : (v : n → K) i = 0 := hv
    have he : (A.updateCol i w) *ᵥ (v : n → K) = A *ᵥ (v : n → K) := by
      funext j
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : k=i
      · subst k
        simp [hcoord]
      · simp [Matrix.updateCol_ne h]
    have hzero : (A.updateCol i w) *ᵥ (v : n → K) = 0 :=
      he.trans v.property
    have hunit : IsUnit (A.updateCol i w) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hdet)
    apply Subtype.ext
    exact (Matrix.mulVec_injective_iff_isUnit.mpr hunit)
      (hzero.trans (Matrix.mulVec_zero _).symm)
  simpa using LinearMap.finrank_le_finrank_of_injective hinj

theorem polynomial_matrix_simple_root_updateCol (A : Matrix n n K[X])
    (φ : K →+* L) (x : L)
    (hd : (derivative A.det).eval₂ φ x ≠ 0) :
    ∃ i : n, ((A.map (Polynomial.eval₂RingHom φ x)).updateCol i
      (fun j => (derivative (A j i)).eval₂ φ x)).det ≠ 0 := by
  let ev : K[X] →+* L := Polynomial.eval₂RingHom φ x
  have hd' : ev (derivative A.det) ≠ 0 := hd
  rw [polynomial_det_derivative_columns, map_sum] at hd'
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero hd'
  refine ⟨i, ?_⟩
  have he : ev ((A.updateCol i (fun j => derivative (A j i))).det) =
      ((A.map ev).updateCol i (fun j => ev (derivative (A j i)))).det := by
    rw [RingHom.map_det]
    congr 1
    exact Matrix.map_updateCol ev
  exact he ▸ hi

theorem polynomial_matrix_separable_root_kernel_finrank (A : Matrix n n K[X])
    (φ : K →+* L) (x : L) (hs : A.det.Separable) (hx : A.det.eval₂ φ x=0) :
    Module.finrank L (LinearMap.ker
      (Matrix.toLin' (A.map (Polynomial.eval₂RingHom φ x)))) = 1 := by
  let E := A.map (Polynomial.eval₂RingHom φ x)
  obtain ⟨i, hi⟩ := polynomial_matrix_simple_root_updateCol A φ x
    (hs.eval₂_derivative_ne_zero φ hx)
  have hle := matrix_kernel_finrank_le_one_of_updateCol_det_ne_zero E i _ hi
  have hdet : E.det=0 := by
    exact ((Polynomial.eval₂RingHom φ x).map_det A).symm.trans hx
  have hker : ⊥ < LinearMap.ker (Matrix.toLin' E) :=
    LinearMap.bot_lt_ker_of_det_eq_zero (by rwa [LinearMap.det_toLin'])
  have hpos : 0 < Module.finrank L (LinearMap.ker (Matrix.toLin' E)) := by
    exact Module.finrank_pos_iff.mpr (Submodule.nontrivial_iff_ne_bot.mpr (ne_of_gt hker))
  exact Nat.le_antisymm hle hpos

end FD56
