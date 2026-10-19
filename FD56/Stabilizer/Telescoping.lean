/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.RankOne

/-! Finite telescoping identities for polynomial kernel constructions.
These identities establish the equations, not completeness or degree bounds. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]

theorem telescoping_commutator (M : Matrix n n R) (P : Matrix m n R)
    (X : ℕ → Matrix n n R) (W : ℕ → Matrix n m R) (q : ℕ)
    (hzero : X 0 * M = W 0 * P)
    (hstep : ∀ i < q, X (i + 1) * M = M * X i + W (i + 1) * P) :
    M * (∑ i ∈ Finset.range (q + 1), X i) -
      (∑ i ∈ Finset.range (q + 1), X i) * M =
      M * X q - (∑ i ∈ Finset.range (q + 1), W i) * P := by
  induction q with
  | zero => simp [hzero]
  | succ q ih =>
    have hi := ih (fun i hi => hstep i (Nat.lt_trans hi (Nat.lt_succ_self q)))
    have hs := hstep q (Nat.lt_succ_self q)
    simp only [Finset.sum_range_succ] at hi ⊢
    calc
      _ = (M * ((∑ i ∈ Finset.range q, X i) + X q) -
            ((∑ i ∈ Finset.range q, X i) + X q) * M) +
            M * X (q + 1) - X (q + 1) * M := by noncomm_ring
      _ = _ := by rw [hi, hs]; simp only [Matrix.add_mul]; abel

theorem telescoping_kernel (M : Matrix n n R) (P : Matrix m n R)
    (X : ℕ → Matrix n n R) (W : ℕ → Matrix n m R)
    (U : Matrix n m R) (q : ℕ)
    (hzero : X 0 * M = W 0 * P)
    (hstep : ∀ i < q, X (i + 1) * M = M * X i + W (i + 1) * P)
    (hend : M * X q = U * P)
    (hP : ∀ i < q + 1, P * X i = 0) :
    P * (∑ i ∈ Finset.range (q + 1), X i) = 0 ∧
      M * (∑ i ∈ Finset.range (q + 1), X i) -
        (∑ i ∈ Finset.range (q + 1), X i) * M =
        (U - ∑ i ∈ Finset.range (q + 1), W i) * P := by
  constructor
  · rw [Matrix.mul_sum]
    exact Finset.sum_eq_zero (fun i hi => hP i (Finset.mem_range.mp hi))
  · rw [telescoping_commutator M P X W q hzero hstep, hend, Matrix.sub_mul]

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq n]

/-- The structured construction for any positive number of Krylov terms. -/
theorem structured_kernel (M : Matrix n n R) (P : Matrix m n R)
    (V : Matrix n r R) (C : Matrix r s R)
    (H : ℕ → Matrix s n R) (D : ℕ → Matrix s m R)
    (T : Matrix s m R) (q : ℕ)
    (hzero : H 0 * M = D 0 * P)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    P * (∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) = 0 ∧
      M * (∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) -
        (∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) * M =
        (M ^ (q + 1) * V * C * T -
          ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * D i) * P := by
  apply telescoping_kernel M P (fun i => M ^ i * V * C * H i)
    (fun i => M ^ i * V * C * D i) (M ^ (q + 1) * V * C * T) q
  · simp only [Matrix.mul_assoc, hzero]
  · intro i hi
    simp only [Matrix.mul_assoc, hstep i hi, Matrix.mul_add, pow_succ']
  · simp only [hend, pow_succ', Matrix.mul_assoc]
  · intro i hi
    calc
      _ = (P * M ^ i * V) * C * H i := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hobs i hi]; simp

/-- Multiplication by PM isolates the last Krylov term. -/
theorem structured_kernel_recovery (M : Matrix n n R) (P : Matrix m n R)
    (V : Matrix n r R) (C : Matrix r s R)
    (H : ℕ → Matrix s n R) (T : Matrix s m R) (q : ℕ)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    P * M * (∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) =
      (P * M ^ (q + 1) * V) * C * (T * P) := by
  rw [Matrix.mul_sum]
  rw [Finset.sum_eq_single q]
  · simp only [hend, pow_succ', Matrix.mul_assoc]
  · intro i hi hne
    have hlt : i + 1 < q + 1 := by have := Finset.mem_range.mp hi; omega
    calc
      _ = (P * M ^ (i + 1) * V) * C * H i := by
        simp only [pow_succ', Matrix.mul_assoc]
      _ = 0 := by rw [hobs (i + 1) hlt]; simp
  · intro h
    exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_self q)))

/-- Explicit one-sided inverses make the construction injective in C. -/
theorem structured_kernel_injective [DecidableEq r] [DecidableEq s]
    (M : Matrix n n R) (P : Matrix m n R) (V : Matrix n r R)
    (H : ℕ → Matrix s n R) (T : Matrix s m R) (q : ℕ)
    (hend : H q = T * P)
    (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (L : Matrix r m R) (B : Matrix n s R)
    (hL : L * (P * M ^ (q + 1) * V) = 1)
    (hB : (T * P) * B = 1) :
    Function.Injective (fun C : Matrix r s R =>
      ∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) := by
  intro C₁ C₂ h
  have h₁ := structured_kernel_recovery M P V C₁ H T q hend hobs
  have h₂ := structured_kernel_recovery M P V C₂ H T q hend hobs
  have hF := h₁.symm.trans ((congrArg (fun A => P * M * A) h).trans h₂)
  have hh := congrArg (fun A => L * A * B) hF
  have cancel (C : Matrix r s R) :
      L * ((P * M ^ (q + 1) * V) * C * (T * P)) * B = C := by
    rw [← Matrix.mul_assoc L, ← Matrix.mul_assoc L, hL, Matrix.one_mul,
      Matrix.mul_assoc, hB, Matrix.mul_one]
  simpa only [cancel] using hh

omit [Fintype r] [Fintype s] in
theorem structured_diagonal_vanishes
    (M : Matrix n n R) (P : Matrix m n R) (V : Matrix n r R)
    (H : ℕ → Matrix s n R) (D : ℕ → Matrix s m R) (T : Matrix s m R) (q : ℕ)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0)
    (i : ℕ) (hi : i ≤ q) : H i * M ^ i * V = 0 := by
  induction hi using Nat.decreasingInduction with
  | self =>
    rw [hend]
    calc
      _ = T * (P * M ^ q * V) := by simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hobs q (Nat.lt_succ_self q), Matrix.mul_zero]
  | of_succ k hk ih =>
    have heq : H (k + 1) * M ^ (k + 1) * V = H k * M ^ k * V := by
      calc
        _ = (H (k + 1) * M) * M ^ k * V := by
          simp only [pow_succ', Matrix.mul_assoc]
        _ = (H k + D (k + 1) * P) * M ^ k * V := by rw [hstep k hk]
        _ = H k * M ^ k * V + D (k + 1) * (P * M ^ k * V) := by
          simp only [Matrix.add_mul, Matrix.mul_assoc]
        _ = _ := by rw [hobs k (by omega), Matrix.mul_zero, add_zero]
    exact heq.symm.trans ih

theorem structured_kernel_trace_zero
    (M : Matrix n n R) (P : Matrix m n R) (V : Matrix n r R) (C : Matrix r s R)
    (H : ℕ → Matrix s n R) (D : ℕ → Matrix s m R) (T : Matrix s m R) (q : ℕ)
    (hstep : ∀ i < q, H (i + 1) * M = H i + D (i + 1) * P)
    (hend : H q = T * P) (hobs : ∀ i < q + 1, P * M ^ i * V = 0) :
    Matrix.trace (∑ i ∈ Finset.range (q + 1), M ^ i * V * C * H i) = 0 := by
  rw [Matrix.trace_sum]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Matrix.trace_mul_comm]
  have hz := structured_diagonal_vanishes M P V H D T q hstep hend hobs i
    (by have := Finset.mem_range.mp hi; omega)
  have heq : H i * (M ^ i * V * C) = (H i * M ^ i * V) * C := by
    simp only [Matrix.mul_assoc]
  rw [heq, hz, Matrix.zero_mul, Matrix.trace_zero]

end FD56
