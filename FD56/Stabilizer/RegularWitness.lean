/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservableRadical
import FD56.Stabilizer.GLWitness

/-! The consecutive observability conditions have explicit witnesses at
every depth, including zero remainder. -/

noncomputable section
namespace FD56
open Matrix
universe u
variable {K : Type*} {m r : Type u} [Field K] [Fintype m] [Fintype r]
  [DecidableEq m] [DecidableEq r]

omit [DecidableEq r] in
theorem glWitness_unobservable_finrank (D : Matrix r r K) (B : Matrix m r K)
    (depth t : ℕ) :
    Module.finrank K (unobservableSpace (glWitness D B depth).1 (glWitness D B depth).2 (depth + t)) =
      Module.finrank K (unobservableSpace D B t) := by
  induction depth with
  | zero => rw [zero_add]; rfl
  | succ depth ih =>
    have heq : depth + 1 + t = (depth + t) + 1 := by omega
    rw [heq]
    exact (unobservable_block_finrank 0 (glWitness D B depth).2 0
      (glWitness D B depth).1 (depth + t)).trans ih

theorem glWitness_observability_profile (D : Matrix r r K) (B : Matrix m r K)
    (L : Matrix r m K) (hL : L * B = 1) (depth : ℕ) :
    Module.finrank K (unobservableSpace (glWitness D B depth).1 (glWitness D B depth).2 depth) =
      Fintype.card r ∧
    Module.finrank K (unobservableSpace (glWitness D B depth).1 (glWitness D B depth).2 (depth + 1)) = 0 := by
  have hB : Function.Injective B.mulVec := by
    intro v w h
    have hh := congrArg (fun z => L *ᵥ z) h
    simpa only [Matrix.mulVec_mulVec, hL, Matrix.one_mulVec] using hh
  have hk : LinearMap.ker (Matrix.toLin' B) = ⊥ := LinearMap.ker_eq_bot.mpr hB
  constructor
  · simpa [unobservableSpace] using glWitness_unobservable_finrank D B depth 0
  · have h := glWitness_unobservable_finrank D B depth 1
    have he : unobservableSpace D B 1 = LinearMap.ker (Matrix.toLin' B) := by
      simp [unobservableSpace, Matrix.toLin'_apply']
    rw [he, hk] at h
    simpa using h

theorem exists_regular_observability_pair {r s : Type} [Fintype r] [Fintype s]
    (q : ℕ) :
    ∃ (M : Matrix (blockIndex (r ⊕ s) r (q + 1))
        (blockIndex (r ⊕ s) r (q + 1)) K)
      (P : Matrix (r ⊕ s) (blockIndex (r ⊕ s) r (q + 1)) K),
      Module.finrank K (unobservableSpace M P (q + 1)) = Fintype.card r ∧
      Module.finrank K (unobservableSpace M P (q + 2)) = 0 := by
  classical
  let B : Matrix (r ⊕ s) r K := Matrix.fromRows 1 0
  let L : Matrix r (r ⊕ s) K := Matrix.fromCols 1 0
  have hL : L * B = 1 := by simp [L, B, Matrix.fromCols_mul_fromRows]
  refine ⟨(glWitness 0 B (q + 1)).1, (glWitness 0 B (q + 1)).2, ?_⟩
  exact glWitness_observability_profile 0 B L hL (q + 1)

end FD56
