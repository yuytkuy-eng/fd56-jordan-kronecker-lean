/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Kirillov

/-! A contradiction to the balanced Hilbert-profile prediction. The Hilbert
function below is defined using the actual polynomial stabilizer equations. -/

noncomputable section
open Matrix Polynomial
open scoped BigOperators

namespace FD56
variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [Fintype n]

def boundedMatrixOf (A : Matrix m n K[X]) {d : ℕ} (hA : DegreeBound A d) :
    BoundedMatrix K m n d := fun i j => boundedPolyOf (A i j) (hA i j)

omit [Fintype m] [Fintype n] in
@[simp] theorem entries_boundedMatrixOf (A : Matrix m n K[X]) {d : ℕ}
    (hA : DegreeBound A d) : entries (boundedMatrixOf A hA) = A := rfl

def boundedSLKernel (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) :
    Submodule K (BoundedMatrix K n n d × BoundedMatrix K n m d) where
  carrier := {z | SLRadical M P (entries z.1) (entries z.2)}
  zero_mem' := by simp [SLRadical, kirillov]
  add_mem' := by
    intro a b ha hb
    refine ⟨?_, ?_⟩
    · change Matrix.trace (entries a.1 + entries b.1) = 0
      rw [Matrix.trace_add, ha.1, hb.1, add_zero]
    · intro Y W hY
      change kirillov M P (entries a.1 + entries b.1)
        (entries a.2 + entries b.2) Y W = 0
      rw [kirillov_add, ha.2 Y W hY, hb.2 Y W hY, add_zero]
  smul_mem' := by
    intro c a ha
    refine ⟨?_, ?_⟩
    · change Matrix.trace (c • entries a.1) = 0
      rw [Matrix.trace_smul, ha.1, smul_zero]
    · intro Y W hY
      change kirillov M P (c • entries a.1) (c • entries a.2) Y W = 0
      rw [kirillov_smul, ha.2 Y W hY, smul_zero]

/-- Dimension of the degree-at-most-d polynomial vectors in the full SL radical. -/
def slHilbert (M : Matrix n n K[X]) (P : Matrix m n K[X]) (d : ℕ) : ℕ :=
  Module.finrank K (boundedSLKernel M P d)

theorem slHilbert_pos_of_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) {d : ℕ}
    (X : Matrix n n K[X]) (U : Matrix n m K[X])
    (hX : X ≠ 0) (hdX : DegreeBound X d) (hdU : DegreeBound U d)
    (hstab : TraceZeroStabilizer M P X U) : 0 < slHilbert M P d := by
  unfold slHilbert
  apply (Module.finrank_pos_iff_exists_ne_zero (R := K)
    (M := boundedSLKernel M P d)).mpr
  let z : boundedSLKernel M P d :=
    ⟨(boundedMatrixOf X hdX, boundedMatrixOf U hdU),
      strict_stabilizer_mem_radical M P X U hstab⟩
  refine ⟨z, ?_⟩
  intro hz
  apply hX
  exact congrArg (fun a : boundedSLKernel M P d => entries a.val.1) hz

theorem family_slHilbert_five_pos (k : ℕ) (hk : 0 < k)
    (M : Matrix (Fin (11 * k)) (Fin (11 * k)) K[X])
    (P : Matrix (Fin (8 * k)) (Fin (11 * k)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (hrow : RowIndependent P) :
    0 < slHilbert M P 5 := by
  obtain ⟨X, U, hX, hdX, hdU, hs⟩ :=
    family_has_degree_five_stabilizer k hk M P hM hP hrow
  exact slHilbert_pos_of_witness M P X U hX hdX hdU hs

def Balanced {ι : Type*} (e : ι → ℕ) : Prop := ∀ i j, e i ≤ e j + 1

def profile {ι : Type*} [Fintype ι] (e : ι → ℕ) (d : ℕ) : ℕ :=
  ∑ i, (d + 1 - e i)

/-- The usual minimal-index Hilbert-function identity, stated explicitly.
This definition does not assert a Jordan--Kronecker decomposition theorem. -/
def HasHilbertProfile {ι : Type*} [Fintype ι]
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (e : ι → ℕ) : Prop :=
  ∀ d, slHilbert M P d = profile e d

theorem balanced_lower_bound {ι : Type*} [Fintype ι] (e : ι → ℕ)
    (he : Balanced e) (a : ℕ) (hsum : a * Fintype.card ι ≤ ∑ i, e i) :
    ∀ i, a ≤ e i := by
  intro i
  by_contra hi
  have hstrict : e i < a := Nat.lt_of_not_ge hi
  have hall : ∀ j, e j ≤ a := by
    intro j
    have := he j i
    omega
  have hlt : (∑ j, e j) < ∑ _j : ι, a := by
    apply Finset.sum_lt_sum
    · intro j _
      exact hall j
    · exact ⟨i, Finset.mem_univ i, hstrict⟩
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul] at hlt
  nlinarith

theorem family_balanced_profile_five_zero {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 0 < k) (e : ι → ℕ) (he : Balanced e)
    (hlen : Fintype.card ι = 15 * k ^ 2 + 1)
    (hsum : (∑ i, e i) = 97 * k ^ 2 - 1) : profile e 5 = 0 := by
  have hk2 : 0 < k ^ 2 := pow_pos hk _
  have hlower : 6 * Fintype.card ι ≤ ∑ i, e i := by
    rw [hlen, hsum]
    omega
  have he6 := balanced_lower_bound e he 6 hlower
  apply Finset.sum_eq_zero
  intro i _
  exact Nat.sub_eq_zero_of_le (he6 i)

/-- No balanced list of the conjectured length and sum describes the actual
polynomial kernel, for any affine full-row-rank pair in this family. -/
theorem family_no_balanced_profile {ι : Type*} [Fintype ι]
    (k : ℕ) (hk : 0 < k)
    (M : Matrix (Fin (11 * k)) (Fin (11 * k)) K[X])
    (P : Matrix (Fin (8 * k)) (Fin (11 * k)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (hrow : RowIndependent P)
    (e : ι → ℕ) (hlen : Fintype.card ι = 15 * k ^ 2 + 1)
    (hsum : (∑ i, e i) = 97 * k ^ 2 - 1) :
    ¬ (Balanced e ∧ HasHilbertProfile M P e) := by
  rintro ⟨he, hprofile⟩
  have hpos := family_slHilbert_five_pos k hk M P hM hP hrow
  have hzero := family_balanced_profile_five_zero k hk e he hlen hsum
  rw [hprofile 5, hzero] at hpos
  exact Nat.lt_irrefl 0 hpos

end FD56
