/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-! Complementary injective and surjective matrices have a simultaneous
constant change of coordinates to the standard inclusion and projection. -/

noncomputable section
namespace FD56
open Matrix

variable {K r s : Type*} [Field K] [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

theorem exists_dual_matrix_normalization
    (F : Matrix (r ⊕ s) r K) (T : Matrix s (r ⊕ s) K)
    (hTF : T * F = 0) (hF : Function.Injective F.mulVec)
    (hT : Function.Surjective T.mulVec) :
    ∃ H J : Matrix (r ⊕ s) (r ⊕ s) K,
      H * J = 1 ∧ J * H = 1 ∧
      J * F = Matrix.fromRows (1 : Matrix r r K) (0 : Matrix s r K) ∧
      T * H = Matrix.fromCols (0 : Matrix s r K) (1 : Matrix s s K) ∧
      H * Matrix.fromRows (1 : Matrix r r K) (0 : Matrix s r K) = F := by
  obtain ⟨q, hq⟩ := (Matrix.toLin' T).exists_rightInverse_of_surjective
    (LinearMap.range_eq_top.mpr hT)
  let Q : Matrix (r ⊕ s) s K := LinearMap.toMatrix' q
  have hTQ : T * Q = 1 := by
    apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_one, Q, Matrix.toLin'_toMatrix'] using hq
  let H := Matrix.fromCols F Q
  have hH (x : (r ⊕ s) → K) :
      H *ᵥ x = F *ᵥ (fun j => x (Sum.inl j)) + Q *ᵥ (fun i => x (Sum.inr i)) := by
    have hx : x = Sum.elim (fun j => x (Sum.inl j)) (fun i => x (Sum.inr i)) := by
      funext i
      cases i <;> rfl
    conv_lhs => rw [hx]
    exact Matrix.fromCols_mulVec_sumElim F Q _ _
  have hHinj : Function.Injective (Matrix.toLin' H) := by
    apply LinearMap.ker_eq_bot.mp
    apply LinearMap.ker_eq_bot'.mpr
    intro x hx
    change H *ᵥ x = 0 at hx
    have hright : (fun i => x (Sum.inr i)) = 0 := by
      have hh := congrArg T.mulVec hx
      rw [hH, Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
        hTF, hTQ] at hh
      simpa using hh
    have hleft : (fun j => x (Sum.inl j)) = 0 := by
      apply hF
      rw [hH, hright] at hx
      simpa using hx
    funext i
    cases i with
    | inl j => exact congrFun hleft j
    | inr j => exact congrFun hright j
  let E := LinearEquiv.ofInjectiveEndo (Matrix.toLin' H) hHinj
  let J := LinearMap.toMatrix' E.symm.toLinearMap
  have hHJ : H * J = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_mul, Matrix.toLin'_one, J, Matrix.toLin'_toMatrix',
      LinearMap.comp_apply, LinearMap.id_apply]
    exact E.apply_symm_apply x
  have hJH : J * H = 1 := by
    apply Matrix.toLin'.injective
    apply LinearMap.ext
    intro x
    simp only [Matrix.toLin'_mul, Matrix.toLin'_one, J, Matrix.toLin'_toMatrix',
      LinearMap.comp_apply, LinearMap.id_apply]
    exact E.symm_apply_apply x
  have hHF : H * Matrix.fromRows (1 : Matrix r r K) (0 : Matrix s r K) = F := by
    simp [H, Matrix.fromCols_mul_fromRows]
  refine ⟨H, J, hHJ, hJH, ?_, ?_, hHF⟩
  · rw [← hHF, ← Matrix.mul_assoc, hJH, Matrix.one_mul]
  · simp [H, hTF, hTQ]

end FD56
