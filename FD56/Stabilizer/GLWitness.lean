/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLBase

/-! Explicit matrix pairs with the nondivisible GL stabilizer dimension.
These witnesses do not assert genericity or a polynomial minimal-index profile. -/

noncomputable section
namespace FD56
open Matrix
universe u

def blockIndex (m r : Type u) : ℕ → Type u
  | 0 => r
  | q + 1 => m ⊕ blockIndex m r q

instance blockIndexDecidableEq (m r : Type u) (q : ℕ) :
    DecidableEq (blockIndex m r q) := Classical.decEq _

instance blockIndexFintype (m r : Type u) [Fintype m] [Fintype r] :
    (q : ℕ) → Fintype (blockIndex m r q)
  | 0 => inferInstanceAs (Fintype r)
  | q + 1 => by
      letI := blockIndexFintype m r q
      exact inferInstanceAs (Fintype (m ⊕ blockIndex m r q))

variable {K : Type*} {m r : Type u} [Field K] [Fintype m] [Fintype r] [DecidableEq m]

def glWitness (D : Matrix r r K) (B : Matrix m r K) :
    (q : ℕ) → Matrix (blockIndex m r q) (blockIndex m r q) K ×
      Matrix m (blockIndex m r q) K
  | 0 => (D, B)
  | q + 1 => (Matrix.fromBlocks 0 (glWitness D B q).2 0 (glWitness D B q).1,
      Matrix.fromCols 1 0)

omit [DecidableEq m] in
theorem blockIndex_card (q : ℕ) :
    Fintype.card (blockIndex m r q) = q * Fintype.card m + Fintype.card r := by
  induction q with
  | zero => simp [blockIndex, blockIndexFintype]
  | succ q ih =>
    change Fintype.card (m ⊕ blockIndex m r q) = _
    rw [Fintype.card_sum, ih]
    ring

theorem glWitness_finrank [DecidableEq r]
    (D : Matrix r r K) (B : Matrix m r K) (L : Matrix r m K)
    (hL : L * B = 1) (q : ℕ) :
    Module.finrank K (glStabilizerSpace (glWitness D B q).1 (glWitness D B q).2) =
      Fintype.card r * (Fintype.card m - Fintype.card r) := by
  induction q with
  | zero => exact gl_base_finrank D B L hL
  | succ q ih =>
    exact (gl_block_finrank 0 (glWitness D B q).2 0 (glWitness D B q).1).trans ih

theorem glWitness_row_surjective (D : Matrix r r K) (B : Matrix m r K) (q : ℕ) :
    Function.Surjective (glWitness D B (q + 1)).2.mulVec := by
  intro y
  refine ⟨Sum.elim y 0, ?_⟩
  change (Matrix.fromCols 1 0) *ᵥ Sum.elim y 0 = y
  simp [Matrix.mulVec, dotProduct, Fintype.sum_sum_type]

theorem glWitness_trace_zero [DecidableEq r]
    (D : Matrix r r K) (B : Matrix m r K) (L : Matrix r m K)
    (hL : L * B = 1) (q : ℕ)
    (z : glStabilizerSpace (glWitness D B q).1 (glWitness D B q).2) :
    Matrix.trace z.val.1 = 0 := by
  induction q with
  | zero =>
    change glStabilizerSpace D B at z
    have hz : B * z.val.1 = 0 := z.property.1
    have h := congrArg (fun T => L * T) hz
    have hG : z.val.1 = 0 := by
      simpa only [← Matrix.mul_assoc, hL, Matrix.one_mul, Matrix.mul_zero] using h
    rw [hG, Matrix.trace_zero]
  | succ q ih =>
    have hz := (gl_block_coordinates 0 (glWitness D B q).2 0
      (glWitness D B q).1 z.val.1 z.val.2).mp z.property
    have ht := ih ⟨(z.val.1.toBlocks₂₂, z.val.1.toBlocks₂₁), hz.2.2.1⟩
    have h11 := hz.1
    change Matrix.trace (z.val.1.toBlocks₂₂) = 0 at ht
    calc
      Matrix.trace z.val.1 = Matrix.trace z.val.1.toBlocks₁₁ +
          Matrix.trace z.val.1.toBlocks₂₂ := by
        exact Fintype.sum_sum_type (fun i : m ⊕ blockIndex m r q => z.val.1 i i)
      _ = 0 := by rw [h11, Matrix.trace_zero, ht, zero_add]

theorem exists_gl_stabilizer_witness {s : Type u} [Fintype s] [DecidableEq r]
    [DecidableEq s] (q : ℕ) :
    ∃ (M : Matrix (blockIndex (r ⊕ s) r (q + 1))
        (blockIndex (r ⊕ s) r (q + 1)) K)
      (P : Matrix (r ⊕ s) (blockIndex (r ⊕ s) r (q + 1)) K),
      Function.Surjective P.mulVec ∧
      Module.finrank K (glStabilizerSpace M P) = Fintype.card r * Fintype.card s ∧
      ∀ z : glStabilizerSpace M P, Matrix.trace z.val.1 = 0 := by
  let B : Matrix (r ⊕ s) r K := Matrix.fromRows 1 0
  let L : Matrix r (r ⊕ s) K := Matrix.fromCols 1 0
  have hL : L * B = 1 := by simp [L, B, Matrix.fromCols_mul_fromRows]
  refine ⟨(glWitness 0 B (q + 1)).1, (glWitness 0 B (q + 1)).2,
    glWitness_row_surjective 0 B q, ?_, ?_⟩
  · simpa only [Fintype.card_sum, Nat.add_sub_cancel_left] using
      glWitness_finrank 0 B L hL (q + 1)
  · exact glWitness_trace_zero 0 B L hL (q + 1)

end FD56
