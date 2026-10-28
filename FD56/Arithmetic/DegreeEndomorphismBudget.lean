/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

/-! The dimension of degree-bounded polynomial endomorphisms is minimal
exactly when the degree list is balanced. The excess formula counts ordered
pairs, so it does not require an order on the finite index type. -/

namespace FD56
open scoped BigOperators

def degreeHomWeight (a b : ℕ) : ℕ := if a≤b then b-a+1 else 0

theorem degreeHomWeight_pair (a b : ℕ) :
    degreeHomWeight a b+degreeHomWeight b a=2+(b-a-1)+(a-b-1) := by
  unfold degreeHomWeight
  split_ifs <;> omega

variable {ι : Type*} [Fintype ι]

def degreeEndomorphismDimension (d : ι → ℕ) : ℕ :=
  ∑ i, ∑ j, degreeHomWeight (d i) (d j)

theorem degreeEndomorphismDimension_excess (d : ι → ℕ) :
    degreeEndomorphismDimension d=Fintype.card ι^2+∑ i, ∑ j, (d j-d i-1) := by
  have hswap : (∑ i, ∑ j, degreeHomWeight (d j) (d i))=
      ∑ i, ∑ j, degreeHomWeight (d i) (d j) := Finset.sum_comm
  have eswap : (∑ i, ∑ j, (d i-d j-1))=∑ i, ∑ j, (d j-d i-1) := Finset.sum_comm
  have hp : (∑ i, ∑ j, (degreeHomWeight (d i) (d j)+degreeHomWeight (d j) (d i)))=
      ∑ i, ∑ j, (2+(d j-d i-1)+(d i-d j-1)) := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    exact degreeHomWeight_pair (d i) (d j)
  simp only [Finset.sum_add_distrib] at hp
  rw [hswap,eswap] at hp
  simp only [Finset.sum_const,Finset.card_univ,smul_eq_mul] at hp
  unfold degreeEndomorphismDimension
  nlinarith

theorem degreeEndomorphismDimension_ge_card_sq (d : ι → ℕ) :
    Fintype.card ι^2≤degreeEndomorphismDimension d := by
  rw [degreeEndomorphismDimension_excess]
  omega

theorem degreeEndomorphismDimension_eq_card_sq_iff (d : ι → ℕ) :
    degreeEndomorphismDimension d=Fintype.card ι^2 ↔ ∀ i j, d i≤d j+1 := by
  rw [degreeEndomorphismDimension_excess]
  constructor
  · intro he i j
    have hz : (∑ i, ∑ j, (d j-d i-1))=0 := by omega
    have hj : (∑ k, (d k-d j-1))=0 :=
      (Finset.sum_eq_zero_iff.mp hz) j (Finset.mem_univ _)
    have hi : d i-d j-1=0 := (Finset.sum_eq_zero_iff.mp hj) i (Finset.mem_univ _)
    omega
  · intro h
    have hz : (∑ i, ∑ j, (d j-d i-1))=0 := by
      apply Finset.sum_eq_zero
      intro i _
      apply Finset.sum_eq_zero
      intro j _
      have := h j i
      omega
    rw [hz,Nat.add_zero]

theorem degreeEndomorphismDimension_le_card_sq_iff (d : ι → ℕ) :
    degreeEndomorphismDimension d≤Fintype.card ι^2 ↔ ∀ i j, d i≤d j+1 := by
  constructor
  · intro h
    exact (degreeEndomorphismDimension_eq_card_sq_iff d).mp
      (Nat.le_antisymm h (degreeEndomorphismDimension_ge_card_sq d))
  · intro h
    rw [(degreeEndomorphismDimension_eq_card_sq_iff d).mpr h]

end FD56
