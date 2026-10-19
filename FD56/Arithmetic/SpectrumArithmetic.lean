/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.Tactic

/-! Arithmetic of the classification formulas. These definitions are candidates;
this file does not identify them with the generic geometric spectrum. -/

namespace FD56

def glFormula (n m : ℕ) : List ℕ :=
  let q := n / m
  let r := n % m
  let s := m - r
  let A := m * q * (q + 1) / 2
  let B := A + r * (q + 1)
  let a := A / r
  let u := A % r
  let b := B / s
  let v := B % s
  let E := a + b + q
  let c₀ := (r - u) * (s - v)
  let c₁ := u * (s - v) + (r - u) * v
  let c₂ := u * v
  List.replicate c₀ E ++ List.replicate c₁ (E + 1) ++ List.replicate c₂ (E + 2)

def slFormula (n m : ℕ) : List ℕ :=
  let q := n / m
  let r := n % m
  let s := m - r
  let A := m * q * (q + 1) / 2
  let B := A + r * (q + 1)
  let a := A / r
  let u := A % r
  let b := B / s
  let v := B % s
  let E := a + b + q
  let c₀ := (r - u) * (s - v)
  let c₁ := u * (s - v) + (r - u) * v
  let c₂ := u * v
  if c₂ ≤ E + 2 then
    let length := r * s + 1
    let total := (n * (n + m) - r * s - 2) / 2
    let d := total / length
    let w := total % length
    List.replicate (length - w) d ++ List.replicate w (d + 1)
  else
    List.replicate c₀ E ++ List.replicate (c₁ + E + 3) (E + 1) ++
      List.replicate (c₂ - E - 2) (E + 2)

def blockSizes (indices : List ℕ) : List ℕ := indices.map (fun e => 2 * e + 1)

def familyFormula (k : ℕ) : List ℕ :=
  List.replicate (k ^ 2) 5 ++ List.replicate (6 * k ^ 2 + 8) 6 ++
    List.replicate (8 * k ^ 2 - 7) 7

theorem family_length (k : ℕ) (hk : 0 < k) :
    (familyFormula k).length = 15 * k ^ 2 + 1 := by
  have : 0 < k ^ 2 := pow_pos hk _
  simp only [familyFormula, List.length_append, List.length_replicate]
  omega

theorem family_sum (k : ℕ) (hk : 0 < k) :
    (familyFormula k).sum = 97 * k ^ 2 - 1 := by
  have : 0 < k ^ 2 := pow_pos hk _
  simp only [familyFormula, List.sum_append, List.sum_replicate, smul_eq_mul]
  omega

theorem family_block_dimension (k : ℕ) (hk : 0 < k) :
    (blockSizes (familyFormula k)).sum = (11 * k) * (11 * k + 8 * k) - 1 := by
  have : 0 < k ^ 2 := pow_pos hk _
  simp only [blockSizes, familyFormula, List.map_append, List.map_replicate,
    List.sum_append, List.sum_replicate, smul_eq_mul]
  have hmul : (11 * k) * (11 * k + 8 * k) = 209 * k ^ 2 := by ring
  rw [hmul]
  omega

def BalancedList (xs : List ℕ) : Prop := ∀ a ∈ xs, ∀ b ∈ xs, a ≤ b + 1

theorem family_not_balanced (k : ℕ) (hk : 0 < k) : ¬ BalancedList (familyFormula k) := by
  have hk2 : 0 < k ^ 2 := pow_pos hk _
  have h5 : 5 ∈ familyFormula k := by
    simp [familyFormula, hk.ne']
  have h7 : 7 ∈ familyFormula k := by
    have hn : 8 * k ^ 2 - 7 ≠ 0 := by omega
    simp [familyFormula, hn]
  intro h
  have := h 7 h7 5 h5
  omega

theorem unbalanced_count (E c₀ c₁ c₂ : ℕ) (h : E + 2 < c₂) :
    c₀ + (c₁ + E + 3) + (c₂ - E - 2) = c₀ + c₁ + c₂ + 1 := by omega

theorem unbalanced_degree_sum (E c₀ c₁ c₂ : ℕ) (h : E + 2 < c₂) :
    E * c₀ + (E + 1) * (c₁ + E + 3) + (E + 2) * (c₂ - E - 2) + 1 =
      E * c₀ + (E + 1) * c₁ + (E + 2) * c₂ := by
  have hs : c₂ - E - 2 + E + 2 = c₂ := by omega
  nlinarith [congrArg (fun z => (E + 2) * z) hs]

theorem table_4_3 : blockSizes (glFormula 4 3) = [13, 15] ∧
    blockSizes (slFormula 4 3) = List.replicate 3 9 := by decide

theorem table_8_5 : blockSizes (glFormula 8 5) =
      [15] ++ List.replicate 3 17 ++ List.replicate 2 19 ∧
    blockSizes (slFormula 8 5) = [13] ++ List.replicate 6 15 := by decide

theorem table_11_8 : blockSizes (glFormula 11 8) =
      [11] ++ List.replicate 6 13 ++ List.replicate 8 15 ∧
    blockSizes (slFormula 11 8) = [11] ++ List.replicate 14 13 ++ [15] := by decide

theorem table_16_7 : blockSizes (glFormula 16 7) =
      List.replicate 3 35 ++ List.replicate 5 37 ++ List.replicate 2 39 ∧
    blockSizes (slFormula 16 7) = List.replicate 9 33 ++ List.replicate 2 35 := by decide

theorem table_64_28 : blockSizes (glFormula 64 28) =
      List.replicate 48 35 ++ List.replicate 80 37 ++ List.replicate 32 39 ∧
    blockSizes (slFormula 64 28) = List.replicate 48 35 ++
      List.replicate 100 37 ++ List.replicate 13 39 := by decide

theorem table_43_10 : blockSizes (glFormula 43 10) =
      List.replicate 8 107 ++ List.replicate 10 109 ++ List.replicate 3 111 ∧
    blockSizes (slFormula 43 10) = List.replicate 16 103 ++ List.replicate 6 105 := by decide

end FD56
