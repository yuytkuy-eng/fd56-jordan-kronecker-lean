/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.StructuredLeading
import FD56.Hilbert.ObservabilityGLTerminal

/-! Actual row relations supply the backward rows and their terminal recovery. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R n m s : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem exists_backward_rows_of_relation (M : Matrix n n R) (P : Matrix m n R)
    (L : Matrix s n R) (D : ℕ → Matrix s m R) (q : ℕ)
    (hrel : L * M ^ (q+1) = ∑ i ∈ Finset.range (q+1), D i * P * M ^ i) :
    ∃ H : ℕ → Matrix s n R, H 0 * M = D 0 * P ∧
      (∀ i < q, H (i+1) * M = H i + D (i+1) * P) ∧ H q = L := by
  induction q generalizing L with
  | zero =>
    exact ⟨fun _ => L, by simpa using hrel, by intro i hi; omega, rfl⟩
  | succ q ih =>
    have hl : (L * M - D (q+1) * P) * M ^ (q+1) =
        ∑ i ∈ Finset.range (q+1), D i * P * M ^ i := by
      rw [Matrix.sub_mul, Matrix.mul_assoc L M, ← pow_succ', hrel,
        Finset.sum_range_succ, add_sub_cancel_right]
    obtain ⟨H,hzero,hstep,hend⟩ := ih (L * M - D (q+1) * P) hl
    refine ⟨fun i => if i ≤ q then H i else L, ?_, ?_, ?_⟩
    · simpa using hzero
    · intro i hi
      by_cases hiq : i < q
      · simpa only [if_pos (show i+1 ≤ q by omega), if_pos (show i ≤ q by omega)]
          using hstep i hiq
      · have he : i = q := by omega
        subst i
        simp only [if_neg (show ¬q+1 ≤ q by omega), if_pos (le_refl q), hend]
        exact (sub_add_cancel (L * M) (D (q+1) * P)).symm
    · simp

theorem backward_rows_terminal_recovery (M : Matrix n n R) (P : Matrix m n R)
    (H : ℕ → Matrix s n R) (D : ℕ → Matrix s m R) (T : Matrix s m R)
    (q : ℕ) (B : Matrix n m R)
    (hstep : ∀ i < q, H (i+1) * M = H i + D (i+1) * P)
    (hend : H q = T * P)
    (hB : ∀ j ≤ q, P * M ^ j * B = if j = q then 1 else 0)
    (i : ℕ) (hi : i ≤ q) :
    ∀ j ≤ i, H i * M ^ j * B = if j = i then T else 0 := by
  induction hi using Nat.decreasingInduction with
  | self =>
    intro j hj
    rw [hend, Matrix.mul_assoc T P, Matrix.mul_assoc T, hB j hj]
    by_cases h : j = q <;> simp [h]
  | of_succ k hk ih =>
    intro j hj
    have he : H k = H (k+1) * M - D (k+1) * P := by
      rw [hstep k hk, add_sub_cancel_right]
    rw [he, Matrix.sub_mul, Matrix.sub_mul]
    have hleft : H (k+1) * M * M ^ j * B = H (k+1) * M ^ (j+1) * B := by
      rw [pow_succ']; simp only [Matrix.mul_assoc]
    have hright : D (k+1) * P * M ^ j * B = 0 := by
      rw [Matrix.mul_assoc (D (k+1)) P, Matrix.mul_assoc, hB j (by omega),
        if_neg (by omega : j ≠ q), Matrix.mul_zero]
    rw [hleft, hright, sub_zero, ih (j+1) (by omega)]
    simp only [Nat.add_right_cancel_iff]

section Polynomial
variable {K r : Type*} [Field K] [Fintype r] [DecidableEq r]

theorem exists_observability_backward_rows
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (q : ℕ)
    (Bv : Basis r K[X] (LinearMap.ker (Matrix.toLin' (observabilityMatrix M P (q+1)))))
    (R : Matrix n (Fin (q+1) × m) K[X]) (hR : observabilityMatrix M P (q+1) * R = 1)
    (T : Matrix s m K[X])
    (hT : T * (P * M ^ (q+1) * polynomialKernelBasisMatrix _ Bv) = 0) :
    ∃ (H : ℕ → Matrix s n K[X]) (D : ℕ → Matrix s m K[X]),
      H 0 * M = D 0 * P ∧
      (∀ i < q, H (i+1) * M = H i + D (i+1) * P) ∧ H q = T * P := by
  let A := T * P * M ^ (q+1) * R
  let D : ℕ → Matrix s m K[X] := fun i =>
    if hi : i < q+1 then Matrix.of fun a b => A a (⟨i,hi⟩,b) else 0
  have hrel : (T * P) * M ^ (q+1) = ∑ i ∈ Finset.range (q+1), D i * P * M ^ i := by
    have he := observability_beta_relation M P (q+1) Bv R hR T hT
    have hex : A * observabilityMatrix M P (q+1) =
        ∑ i ∈ Finset.range (q+1), D i * (P * M ^ i) := by
      funext a b
      simp only [Matrix.mul_apply, observabilityMatrix, Fintype.sum_prod_type, Matrix.sum_apply]
      rw [← Fin.sum_univ_eq_sum_range]
      apply Finset.sum_congr rfl
      intro i _
      simp only [D, dif_pos i.isLt, Matrix.of_apply]
    rw [show T * P * M ^ (q+1) * R = A from rfl, hex] at he
    simpa only [Matrix.mul_assoc] using he
  obtain ⟨H,hzero,hstep,hend⟩ := exists_backward_rows_of_relation M P (T * P) D q hrel
  exact ⟨H,D,hzero,hstep,hend⟩

end Polynomial
end FD56
