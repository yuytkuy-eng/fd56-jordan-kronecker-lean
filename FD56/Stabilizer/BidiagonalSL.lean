/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BidiagonalPencil

/-! The rectangular bidiagonal pencil supplies a low-degree injectivity
witness for the full SL equations in the range m = n + 1. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem mul_bidiagonal_transpose (n : ℕ)
    (U : Matrix (Fin n) (Fin (n + 1)) K[X]) (i j : Fin n) :
    (U * (bidiagonalPencil (K := K) n).transpose) i j =
      Polynomial.X * U i j.castSucc + U i j.succ := by
  simpa [Matrix.mul_apply, Matrix.mulVec, dotProduct, mul_comm] using
    bidiagonalPencil_mulVec n (U i) j

theorem bidiagonal_scalar_coordinates (n : ℕ)
    (U : Matrix (Fin n) (Fin (n + 1)) K[X]) (c : K[X])
    (hU : U * (bidiagonalPencil n).transpose = c • (1 : Matrix (Fin n) (Fin n) K[X]))
    (i : Fin n) (j : Fin (n + 1)) :
    U i j = (-Polynomial.X) ^ j.val * U i 0 +
      if i.val < j.val then (-Polynomial.X) ^ (j.val - 1 - i.val) * c else 0 := by
  refine Fin.induction ?_ (fun k ih => ?_) j
  · simp
  · have hh := congrArg (fun A : Matrix (Fin n) (Fin n) K[X] => A i k) hU
    change (U * (bidiagonalPencil (K := K) n).transpose) i k = _ at hh
    rw [mul_bidiagonal_transpose] at hh
    change Polynomial.X * U i k.castSucc + U i k.succ =
      c * (if i = k then 1 else 0) at hh
    change U i k.castSucc = (-Polynomial.X) ^ k.val * U i 0 +
      if i.val < k.val then (-Polynomial.X) ^ (k.val - 1 - i.val) * c else 0 at ih
    rw [ih] at hh
    change U i k.succ = (-Polynomial.X) ^ (k.val + 1) * U i 0 +
      if i.val < k.val + 1 then (-Polynomial.X) ^ (k.val + 1 - 1 - i.val) * c else 0
    by_cases he : i = k
    · subst i
      simp only [lt_self_iff_false, if_false, Nat.lt_succ_self, if_true,
        Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul, mul_one, add_zero] at hh ⊢
      rw [pow_succ]
      linear_combination hh
    · have hne : i.val ≠ k.val := fun h => he (Fin.ext h)
      by_cases hlt : i.val < k.val
      · have hs : i.val < k.val + 1 := by omega
        have hp : k.val - i.val = (k.val - 1 - i.val) + 1 := by omega
        simp only [hlt, hs, if_true, he, if_false, mul_zero, Nat.add_sub_cancel] at hh ⊢
        rw [hp, pow_succ, pow_succ]
        linear_combination hh
      · have hs : ¬ i.val < k.val + 1 := by omega
        simp only [hlt, hs, if_false, he, mul_zero, add_zero] at hh ⊢
        rw [pow_succ]
        linear_combination hh

theorem coeff_neg_X_pow_mul (p : K[X]) (e k : ℕ) :
    (((-Polynomial.X : K[X]) ^ e) * p).coeff (e + k) = (-1 : K) ^ e * p.coeff k := by
  have he : (-Polynomial.X : K[X]) ^ e = Polynomial.C ((-1 : K) ^ e) * Polynomial.X ^ e := by
    rw [map_pow, ← mul_pow]
    congr 1
    simp
  rw [he, mul_assoc, Polynomial.coeff_C_mul]
  rw [Polynomial.coeff_X_pow_mul']
  simp

theorem bidiagonal_scalar_low_degree_zero (n d : ℕ) (hd : d + 1 < n)
    (U : Matrix (Fin n) (Fin (n + 1)) K[X]) (c : K[X])
    (hU : U * (bidiagonalPencil n).transpose = c • (1 : Matrix (Fin n) (Fin n) K[X]))
    (hdeg : DegreeBound U d) : U = 0 ∧ c = 0 := by
  have hn : 0 < n := by omega
  have hcdeg : c.natDegree ≤ d + 1 := by
    let i : Fin n := ⟨0, hn⟩
    have hh := congrArg (fun A : Matrix (Fin n) (Fin n) K[X] => A i i) hU
    have hb : DegreeBound (U * (bidiagonalPencil n).transpose) (d + 1) :=
      degreeBound_mul hdeg (fun i j => bidiagonalPencil_degree n j i)
    have he : (U * (bidiagonalPencil (K := K) n).transpose) i i = c := by simpa using hh
    rw [← he]
    exact hb i i
  have hc : c = 0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k < n
    · let i : Fin n := ⟨k, hk⟩
      have hh := bidiagonal_scalar_coordinates n U c hU i (Fin.last n)
      have hs : n - 1 = (n - 1 - k) + k := by omega
      have hh' := congrArg (fun p : K[X] => p.coeff (n - 1)) hh
      have hz : (U i (Fin.last n)).coeff (n - 1) = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg i _) (by omega))
      have hp : (((-Polynomial.X : K[X]) ^ n) * U i 0).coeff (n - 1) = 0 := by
        have he : (-Polynomial.X : K[X]) ^ n = Polynomial.C ((-1 : K) ^ n) * Polynomial.X ^ n := by
          rw [map_pow, ← mul_pow]; congr 1; simp
        rw [he, mul_assoc, Polynomial.coeff_C_mul]
        rw [Polynomial.coeff_X_pow_mul']
        simp [show ¬ n ≤ n - 1 by omega]
      simp only [Fin.val_last, i, show k < n from hk, if_true, Polynomial.coeff_add] at hh'
      rw [hz, hp, zero_add] at hh'
      have ht := coeff_neg_X_pow_mul c (n - 1 - k) k
      rw [← hs] at ht
      rw [ht] at hh'
      have hs' : (-1 : K) ^ (n - 1 - k) ≠ 0 := pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero)
      simpa using (mul_eq_zero.mp hh'.symm).resolve_left hs'
    · simpa using Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hcdeg (by omega : d + 1 < k))
  refine ⟨?_, hc⟩
  funext i j
  have hker : bidiagonalPencil n *ᵥ U i = 0 := by
    funext k
    have hh := congrArg (fun A : Matrix (Fin n) (Fin n) K[X] => A i k) hU
    change (U * (bidiagonalPencil (K := K) n).transpose) i k = _ at hh
    rw [mul_bidiagonal_transpose, hc] at hh
    simpa [bidiagonalPencil_mulVec] using hh
  have hz := (bidiagonalPencil_degree_iff n d (U i) hker).mp (hdeg i)
  have hz₀ : U i 0 = 0 := by rcases hz with h | h; exact h; omega
  rw [bidiagonalPencil_kernel_coordinates n (U i) hker j, hz₀, mul_zero]
  rfl

end FD56
