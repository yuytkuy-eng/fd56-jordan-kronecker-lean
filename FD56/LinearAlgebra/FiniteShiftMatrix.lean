/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic

/-! Truncated shifts and their first rows over an arbitrary commutative ring. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R]

def finiteShiftMatrix (N s : ℕ) : Matrix (Fin N) (Fin N) R :=
  fun i j => if i.val+s=j.val then 1 else 0

def finiteInitialRows (m N : ℕ) : Matrix (Fin m) (Fin N) R :=
  fun i j => if i.val=j.val then 1 else 0

@[simp] theorem finiteShiftMatrix_zero (N : ℕ) : finiteShiftMatrix (R := R) N 0=1 := by
  ext i j
  simp [finiteShiftMatrix,Matrix.one_apply,Fin.ext_iff]

theorem finiteShiftMatrix_mul (N a b : ℕ) :
    finiteShiftMatrix (R := R) N a * finiteShiftMatrix N b=finiteShiftMatrix N (a+b) := by
  ext i j
  by_cases h : i.val+a<N
  · let k : Fin N := ⟨i.val+a,h⟩
    rw [Matrix.mul_apply,Finset.sum_eq_single k]
    · simp [finiteShiftMatrix,k,Nat.add_assoc]
    · intro l _ hl
      have hne : i.val+a ≠ l.val := by
        intro he
        apply hl
        apply Fin.ext
        exact he.symm
      simp [finiteShiftMatrix,hne]
    · simp
  · have hne : i.val+(a+b) ≠ j.val := by omega
    rw [Matrix.mul_apply]
    simp only [finiteShiftMatrix,hne,↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    have hk : i.val+a ≠ k.val := by omega
    simp [hk]

theorem finiteShiftMatrix_pow (N a s : ℕ) :
    (finiteShiftMatrix (R := R) N a)^s=finiteShiftMatrix N (a*s) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [pow_succ,ih,finiteShiftMatrix_mul]
    congr 1

theorem finiteInitialRows_mul_shift (m N s : ℕ) :
    finiteInitialRows (R := R) m N * finiteShiftMatrix N s =
      fun (i : Fin m) (j : Fin N) => if i.val+s=j.val then (1 : R) else 0 := by
  ext i j
  by_cases h : i.val<N
  · let k : Fin N := ⟨i.val,h⟩
    rw [Matrix.mul_apply,Finset.sum_eq_single k]
    · simp [finiteInitialRows,finiteShiftMatrix,k]
    · intro l _ hl
      have hne : i.val ≠ l.val := by
        intro he
        apply hl
        apply Fin.ext
        exact he.symm
      simp [finiteInitialRows,hne]
    · simp
  · have hne : i.val+s ≠ j.val := by omega
    rw [Matrix.mul_apply]
    simp only [hne,↓reduceIte]
    apply Finset.sum_eq_zero
    intro k _
    have hk : i.val ≠ k.val := by omega
    simp [finiteInitialRows,hk]

end FD56
