/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RegularDimension
import FD56.Stabilizer.FieldRadical
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-! An observable pair has nilpotent matrix components in its GL stabilizer.
This supplies the trace-zero hypothesis for the full SL radical formula. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

omit [DecidableEq m] [DecidableEq n] in
theorem stabilizer_raises_unobservable (M : Matrix n n K) (P : Matrix m n K)
    (z : glStabilizerSpace M P) (q : ℕ) (v : n → K)
    (hv : v ∈ unobservableSpace M P q) :
    z.val.1 *ᵥ v ∈ unobservableSpace M P (q + 1) := by
  have hp : ∀ w : n → K, P *ᵥ (z.val.1 *ᵥ w) = 0 := by
    intro w
    rw [Matrix.mulVec_mulVec, z.property.1, Matrix.zero_mulVec]
  induction q generalizing v with
  | zero => exact ⟨hp v, Submodule.mem_top⟩
  | succ q ih =>
    obtain ⟨hPv, hMv⟩ := (mem_unobservableSpace_succ M P q v).mp hv
    have hcomm : M *ᵥ (z.val.1 *ᵥ v) = z.val.1 *ᵥ (M *ᵥ v) := by
      have h := congrArg (fun A : Matrix n n K => A *ᵥ v) z.property.2
      simp only [Matrix.sub_mulVec, ← Matrix.mulVec_mulVec, hPv, Matrix.mulVec_zero] at h
      exact sub_eq_zero.mp h
    refine ⟨hp v, ?_⟩
    change M *ᵥ (z.val.1 *ᵥ v) ∈ unobservableSpace M P (q + 1)
    rw [hcomm]
    exact ih (M *ᵥ v) hMv

omit [DecidableEq m] in
theorem stabilizer_power_mem_unobservable (M : Matrix n n K) (P : Matrix m n K)
    (z : glStabilizerSpace M P) (q : ℕ) (v : n → K) :
    z.val.1 ^ q *ᵥ v ∈ unobservableSpace M P q := by
  induction q with
  | zero => exact Submodule.mem_top
  | succ q ih =>
    have h := stabilizer_raises_unobservable M P z q _ ih
    simpa only [Matrix.mulVec_mulVec, ← pow_succ'] using h

omit [DecidableEq m] in
theorem observable_stabilizer_nilpotent (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (hq : unobservableSpace M P q = ⊥) (z : glStabilizerSpace M P) :
    IsNilpotent z.val.1 := by
  refine ⟨q, ?_⟩
  have hlin : Matrix.toLin' (z.val.1 ^ q) = 0 := by
    apply LinearMap.ext
    intro v
    have h := stabilizer_power_mem_unobservable M P z q v
    rw [hq] at h
    exact h
  simpa only [LinearMap.toMatrix'_toLin', map_zero] using congrArg LinearMap.toMatrix' hlin

omit [DecidableEq m] in
theorem observable_stabilizer_trace_zero (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (hq : Module.finrank K (unobservableSpace M P q) = 0)
    (z : glStabilizerSpace M P) : Matrix.trace z.val.1 = 0 :=
  (Matrix.isNilpotent_trace_of_isNilpotent
    (observable_stabilizer_nilpotent M P q (Submodule.finrank_eq_zero.mp hq) z)).eq_zero

theorem observable_sl_radical_finrank [Nonempty n]
    (M : Matrix n n K) (P : Matrix m n K)
    (q : ℕ) (hq : Module.finrank K (unobservableSpace M P q) = 0) :
    Module.finrank K (fieldSLRadical M P) = Module.finrank K (glStabilizerSpace M P) + 1 :=
  fieldSLRadical_finrank M P (observable_stabilizer_trace_zero M P q hq)

theorem sl_finrank_of_observability {n m : Type} [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] [Nonempty n]
    (q ρ : ℕ) (M : Matrix n n K) (P : Matrix m n K)
    (hsize : Fintype.card n = (q + 1) * Fintype.card m + ρ)
    (hfirst : Module.finrank K (unobservableSpace M P (q + 1)) = ρ)
    (hnext : Module.finrank K (unobservableSpace M P (q + 2)) = 0) :
    Module.finrank K (fieldSLRadical M P) = ρ * (Fintype.card m - ρ) + 1 := by
  rw [observable_sl_radical_finrank M P (q + 2) hnext,
    gl_finrank_of_observability q ρ M P hsize hfirst hnext]

end FD56
