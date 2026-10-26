/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Tactic

/-! Exact cyclic determinants for upper Hessenberg matrices. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators

variable {R : Type*} [CommRing R] {n : ℕ}

def firstCyclicMatrix (M : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    Matrix (Fin (n+1)) (Fin (n+1)) R := fun i j => (M^i.val) 0 j

theorem hessenberg_power_first_row_zero
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hM : ∀ i j, i.val+1 < j.val → M i j = 0) (k : ℕ) (j : Fin (n+1))
    (hj : k < j.val) : (M^k) 0 j = 0 := by
  induction k generalizing j with
  | zero =>
    have hj' : (0 : Fin (n+1)) ≠ j := by intro h; simp [← h] at hj
    simp [Matrix.one_apply, hj']
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro i hi
    by_cases hki : k < i.val
    · rw [ih i hki, zero_mul]
    · rw [hM i j (by omega), mul_zero]

theorem hessenberg_power_first_row_step
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hM : ∀ i j, i.val+1 < j.val → M i j = 0) (k : ℕ) (hk : k < n) :
    (M^(k+1)) 0 ⟨k+1,by omega⟩ =
      (M^k) 0 ⟨k,by omega⟩ * M ⟨k,by omega⟩ ⟨k+1,by omega⟩ := by
  rw [pow_succ, Matrix.mul_apply]
  apply Finset.sum_eq_single (⟨k,by omega⟩ : Fin (n+1))
  · intro i hi hik
    by_cases hki : k < i.val
    · rw [hessenberg_power_first_row_zero M hM k i hki, zero_mul]
    · have hik' : i.val ≠ k := by intro h; apply hik; exact Fin.ext h
      rw [hM i ⟨k+1,by omega⟩ (by dsimp; omega), mul_zero]
  · simp

theorem hessenberg_power_first_row_diagonal
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hM : ∀ i j, i.val+1 < j.val → M i j = 0) (k : ℕ) (hk : k ≤ n) :
    (M^k) 0 ⟨k,by omega⟩ =
      ∏ i : Fin k, M ⟨i.val,by omega⟩ ⟨i.val+1,by omega⟩ := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [hessenberg_power_first_row_step M hM k (by omega), ih (by omega)]
    rw [Fin.prod_univ_castSucc]
    rfl

theorem firstCyclicMatrix_det_of_hessenberg
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R)
    (hM : ∀ i j, i.val+1 < j.val → M i j = 0) :
    (firstCyclicMatrix M).det =
      ∏ k : Fin (n+1), ∏ i : Fin k.val, M ⟨i.val,by omega⟩ ⟨i.val+1,by omega⟩ := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_congr rfl
    intro k hk
    exact hessenberg_power_first_row_diagonal M hM k.val (by omega)
  · intro i j hij
    exact hessenberg_power_first_row_zero M hM i.val j hij

theorem firstCyclicMatrix_map {S : Type*} [CommRing S] (f : R →+* S)
    (M : Matrix (Fin (n+1)) (Fin (n+1)) R) :
    (firstCyclicMatrix M).map f = firstCyclicMatrix (M.map f) := by
  ext i j
  change f ((M^i.val) 0 j) = ((M.map f)^i.val) 0 j
  have hpow : (M^i.val).map f = (M.map f)^i.val := map_pow f.mapMatrix M i.val
  exact congrFun (congrFun hpow 0) j

end FD56
