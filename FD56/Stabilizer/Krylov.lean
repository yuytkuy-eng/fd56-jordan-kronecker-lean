/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.Telescoping

/-! Observability gives independence of the Krylov blocks used in the
leading-coefficient argument for the structured polynomial kernel. -/

namespace FD56
open Matrix
open scoped BigOperators

theorem krylov_blocks_independent {R n m r s : Type*}
    [CommRing R] [Fintype n] [Fintype m] [Fintype r] [DecidableEq n]
    (M : Matrix n n R) (V : Matrix n r R) (q : ℕ)
    (P : Matrix m n R)
    (hobs : ∀ i < q, P * M ^ i * V = 0)
    (hF : Function.Injective (fun C : Matrix r s R => (P * M ^ q * V) * C))
    (U : ℕ → Matrix r s R)
    (hsum : ∑ i ∈ Finset.range q, M ^ i * V * U i = 0) :
    ∀ i < q, U i = 0 := by
  induction q generalizing P with
  | zero => intro i hi; omega
  | succ q ih =>
    have hlast : (P * M ^ (q + 1) * V) * U q = 0 := by
      have heval : P * M * (∑ i ∈ Finset.range (q + 1), M ^ i * V * U i) =
          (P * M ^ (q + 1) * V) * U q := by
        rw [Matrix.mul_sum, Finset.sum_eq_single q]
        · simp only [pow_succ', Matrix.mul_assoc]
        · intro i hi hne
          have hlt : i + 1 < q + 1 := by have := Finset.mem_range.mp hi; omega
          calc
            _ = (P * M ^ (i + 1) * V) * U i := by simp only [pow_succ', Matrix.mul_assoc]
            _ = 0 := by rw [hobs (i + 1) hlt, Matrix.zero_mul]
        · intro h
          exact False.elim (h (Finset.mem_range.mpr (Nat.lt_succ_self q)))
      rw [hsum, Matrix.mul_zero] at heval
      exact heval.symm
    have hq : U q = 0 := hF (hlast.trans (Matrix.mul_zero _).symm)
    have hsmall : ∑ i ∈ Finset.range q, M ^ i * V * U i = 0 := by
      simpa only [Finset.sum_range_succ, hq, Matrix.mul_zero, add_zero] using hsum
    have hobs' : ∀ i < q, (P * M) * M ^ i * V = 0 := by
      intro i hi
      have hh := hobs (i + 1) (by omega)
      simpa only [pow_succ', Matrix.mul_assoc] using hh
    have hF' : Function.Injective (fun C : Matrix r s R => ((P * M) * M ^ q * V) * C) := by
      simpa only [pow_succ', Matrix.mul_assoc] using hF
    have hrest := ih (P * M) hobs' hF' hsmall
    intro i hi
    by_cases heq : i = q
    · simpa only [heq] using hq
    · exact hrest i (by omega)

end FD56
