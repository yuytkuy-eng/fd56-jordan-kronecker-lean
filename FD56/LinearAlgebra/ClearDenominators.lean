/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Integer
import Mathlib.Data.Matrix.Mul

/-! A finite vector over a fraction field has a common nonzero denominator.
Homogeneous matrix equations descend with that vector. -/

noncomputable section
namespace FD56
open Matrix

theorem vector_clear_denominators {R F ι : Type*} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Fintype ι] (v : ι → F) :
    ∃ (d : R) (w : ι → R), d ≠ 0 ∧
      ∀ i, algebraMap R F (w i) = algebraMap R F d * v i := by
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R) v
  choose w hw using hd
  exact ⟨d, w, mem_nonZeroDivisors_iff_ne_zero.mp d.property,
    fun i => (hw i).trans (Algebra.smul_def _ _)⟩

theorem kernel_clear_denominators {R F a b : Type*} [CommRing R] [IsDomain R]
    [Field F] [Algebra R F] [IsFractionRing R F] [Fintype b]
    (A : Matrix a b R) (v : b → F) (hv : (A.map (algebraMap R F)) *ᵥ v = 0) :
    ∃ (d : R) (w : b → R), d ≠ 0 ∧ A *ᵥ w = 0 ∧
      ∀ i, algebraMap R F (w i) = algebraMap R F d * v i := by
  obtain ⟨d, w, hd, hw⟩ := vector_clear_denominators (R := R) v
  refine ⟨d, w, hd, ?_, hw⟩
  have he : (fun i => algebraMap R F (w i)) = algebraMap R F d • v := by
    funext i
    exact hw i
  funext i
  apply IsFractionRing.injective R F
  rw [RingHom.map_mulVec]
  change ((A.map (algebraMap R F)) *ᵥ (fun j => algebraMap R F (w j))) i = _
  rw [he, Matrix.mulVec_smul, hv]
  simp

end FD56
