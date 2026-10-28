/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MonomialPluckerKernel
import FD56.Hilbert.BalancedDegrees

/-! Primitive Plucker rows of every degree with balanced actual syzygy degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def pluckerGapA (W : ℕ) : ℕ := W/5 + if 2≤W%5 then 1 else 0
def pluckerGapB (W : ℕ) : ℕ := W/5 + if W%5=4 then 1 else 0
def pluckerGapC (W : ℕ) : ℕ := W/5 + W%5%2

theorem pluckerGap_sum (W : ℕ) :
    2*pluckerGapA W+2*pluckerGapB W+pluckerGapC W=W := by
  have hmod := Nat.mod_lt W (by decide : 0<5)
  interval_cases h : W%5 <;> simp [pluckerGapA,pluckerGapB,pluckerGapC,h] <;> omega

theorem pluckerGap_balanced (W : ℕ) :
    [pluckerGapA W,pluckerGapB W,pluckerGapC W,pluckerGapB W,pluckerGapA W].Perm
      (balancedDegreeList W 5) := by
  have hmod := Nat.mod_lt W (by decide : 0<5)
  interval_cases h : W%5 <;>
    simp [pluckerGapA,pluckerGapB,pluckerGapC,balancedDegreeList,h]
  all_goals
    apply List.perm_iff_count.mpr
    intro x
    by_cases hx : x=W/5 <;> by_cases hx' : x=W/5+1 <;> simp_all [List.count_cons]
    all_goals omega

variable {K : Type*} [Field K] [CharZero K]

def balancedMonomialPlucker (W : ℕ) : Fin 6 → K[X] :=
  monomialPluckerRow (pluckerGapA W) (pluckerGapB W) (pluckerGapC W)

omit [CharZero K] in
theorem balancedMonomialPlucker_endpoints (W : ℕ) :
    balancedMonomialPlucker (K:=K) W 0=1 ∧
      balancedMonomialPlucker (K:=K) W 5=X^W := by
  simp [balancedMonomialPlucker,monomialPluckerRow,pluckerGap_sum]

theorem balancedMonomialPlucker_degree (W : ℕ) :
    ∀ i, (balancedMonomialPlucker (K:=K) W i).natDegree≤W := by
  have hs := pluckerGap_sum W
  intro i
  fin_cases i <;> simp [balancedMonomialPlucker,monomialPluckerRow] <;> omega

omit [CharZero K] in
theorem balancedMonomialPlucker_relation (W : ℕ) :
    balancedMonomialPlucker (K:=K) W 0 * balancedMonomialPlucker (K:=K) W 5 -
      balancedMonomialPlucker (K:=K) W 1 * balancedMonomialPlucker (K:=K) W 4 +
      balancedMonomialPlucker (K:=K) W 2 * balancedMonomialPlucker (K:=K) W 3 = 0 :=
  monomialPlucker_relation _ _ _

theorem balancedMonomialPlucker_minimal_degrees (W : ℕ) :
    HasMinimalKernelDegrees (fun _ : Unit => balancedMonomialPlucker (K:=K) W)
      (balancedDegreeList W 5) := by
  obtain ⟨r,B,e,hB,hL,hperm⟩ := monomialPlucker_minimal_degrees (K:=K)
    (pluckerGapA W) (pluckerGapB W) (pluckerGapC W)
  exact ⟨r,B,e,hB,hL,hperm.trans (pluckerGap_balanced W)⟩

end FD56
