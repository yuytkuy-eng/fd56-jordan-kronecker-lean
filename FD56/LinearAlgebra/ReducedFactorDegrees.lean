/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PredictableDegree

/-! A bounded product through a reduced column frame bounds every row of its
coefficient matrix. Row independence ensures that no frame degree is unused. -/

namespace FD56
open Matrix Polynomial

variable {K n r s : Type*} [Field K] [Fintype r]

theorem reduced_factor_degree_bounds
    (V : Matrix n r K[X]) (C : Matrix r s K[X]) (e : r → ℕ) (D : ℕ)
    (hV : ∀ i j, (V i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (V i j).coeff (e j))))
    (hC : Function.Injective C.transpose.mulVec)
    (hVC : DegreeBound (V*C) D) :
    (∀ i, e i ≤ D) ∧ ∀ i j, (C i j).natDegree ≤ D-e i := by
  classical
  have hbounds : ∀ i j, C i j=0 ∨ (e i≤D ∧ (C i j).natDegree≤D-e i) := by
    intro i j
    exact (polynomial_combination_degree_iff V e (fun k => C k j) D hV hlead).mp
      (fun k => hVC k j) i
  have hrow : ∀ i, ∃ j, C i j≠0 := by
    intro i
    by_contra! hz
    have hzero : C.transpose *ᵥ Pi.single i 1=C.transpose *ᵥ 0 := by
      funext j
      simpa only [Matrix.mulVec_single_one,Matrix.mulVec_zero,
        Matrix.transpose_apply,Pi.zero_apply] using hz j
    have h := congrFun (hC hzero) i
    simp at h
  constructor
  · intro i
    obtain ⟨j,hj⟩ := hrow i
    exact ((hbounds i j).resolve_left hj).1
  · intro i j
    rcases hbounds i j with hz | ⟨_,hd⟩
    · simp [hz]
    · exact hd

end FD56
