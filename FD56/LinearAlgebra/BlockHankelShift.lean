/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BlockHankel
import Mathlib.Algebra.Polynomial.Coeff
import Mathlib.Algebra.Polynomial.Degree.Lemmas

/-! Multiplication by `X - C z` shifts a truncated Hankel row. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R]

theorem hankel_shift_sum (a : ℕ → R) (q : R[X]) (z : R) (N r : ℕ)
    (hq : q.coeff N = 0) :
    (∑ s : Fin (N+1), a (r+s.val) * ((X-C z)*q).coeff s.val) =
      (∑ s : Fin N, a (r+1+s.val) * q.coeff s.val) -
        z * (∑ s : Fin N, a (r+s.val) * q.coeff s.val) := by
  simp only [sub_mul, coeff_sub, mul_sub, Finset.sum_sub_distrib, coeff_C_mul]
  have hX : (∑ s : Fin (N+1), a (r+s.val) * (X*q).coeff s.val) =
      ∑ s : Fin N, a (r+1+s.val) * q.coeff s.val := by
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, coeff_X_mul_zero, mul_zero, zero_add, Fin.val_succ, coeff_X_mul]
    congr 1
    funext s
    rw [show r+(s.val+1)=r+1+s.val by omega]
  rw [hX, Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc, Fin.val_last, hq, mul_zero, add_zero]
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  ring

def polynomialHankelAction {b c : ℕ} (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R) (q : Fin c → R[X]) (j : Fin b) (r : ℕ) : R :=
  ∑ i, ∑ s : Fin (g i), a j i (r+s.val) * (q i).coeff s.val

theorem polynomialHankelAction_shift {b c : ℕ} (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R) (q : Fin c → R[X]) (z : R)
    (hq : ∀ i, (q i).coeff (g i)=0) (j : Fin b) (r : ℕ) :
    polynomialHankelAction (fun i => g i+1) a (fun i => (X-C z)*q i) j r =
      polynomialHankelAction g a q j (r+1) - z * polynomialHankelAction g a q j r := by
  simp only [polynomialHankelAction, hankel_shift_sum _ _ _ _ _ (hq _),
    Finset.sum_sub_distrib, Finset.mul_sum]

def hankelCoefficientPolynomial {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) : R[X] :=
  ∑ s : Fin (g i), monomial s.val (x ⟨i,s⟩)

theorem hankelCoefficientPolynomial_coeff {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) (s : Fin (g i)) :
    (hankelCoefficientPolynomial g x i).coeff s.val = x ⟨i,s⟩ := by
  simp [hankelCoefficientPolynomial, finset_sum_coeff, coeff_monomial, Fin.val_inj]

theorem hankelCoefficientPolynomial_top_coeff {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) :
    (hankelCoefficientPolynomial g x i).coeff (g i) = 0 := by
  simp only [hankelCoefficientPolynomial, finset_sum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg (Nat.ne_of_lt s.isLt)]

theorem hankelCoefficientPolynomial_high_coeff {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) (k : ℕ) (hk : g i≤k) :
    (hankelCoefficientPolynomial g x i).coeff k = 0 := by
  simp only [hankelCoefficientPolynomial, finset_sum_coeff, coeff_monomial]
  apply Finset.sum_eq_zero
  intro s _
  rw [if_neg (Nat.ne_of_lt (lt_of_lt_of_le s.isLt hk))]

theorem hankelCoefficientPolynomial_degree_lt {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) :
    (hankelCoefficientPolynomial g x i).degree < (g i : WithBot ℕ) := by
  apply (degree_lt_iff_coeff_zero _ _).mpr
  exact fun k hk => hankelCoefficientPolynomial_high_coeff g x i k hk

theorem hankelCoefficientPolynomial_shift_natDegree {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) (z : R) :
    ((X-C z)*hankelCoefficientPolynomial g x i).natDegree ≤ g i := by
  apply natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  cases k with
  | zero => omega
  | succ k =>
    simp only [sub_mul, coeff_sub, coeff_X_mul, coeff_C_mul,
      hankelCoefficientPolynomial_high_coeff g x i k (by omega),
      hankelCoefficientPolynomial_high_coeff g x i (k+1) (by omega), mul_zero, sub_zero]

theorem hankelCoefficientPolynomial_shift_top {c : ℕ} (g : Fin c → ℕ)
    (x : (Σ i, Fin (g i)) → R) (i : Fin c) (z : R) (hi : 0<g i) :
    ((X-C z)*hankelCoefficientPolynomial g x i).coeff (g i) =
      x ⟨i,⟨g i-1,by omega⟩⟩ := by
  have hg : g i-1+1=g i := by omega
  simp only [sub_mul, coeff_sub, coeff_C_mul, hankelCoefficientPolynomial_top_coeff,
    mul_zero, sub_zero]
  conv_lhs => rw [← hg, coeff_X_mul]
  exact hankelCoefficientPolynomial_coeff g x i ⟨g i-1,by omega⟩

theorem hankelCoefficientPolynomial_action {b c : ℕ}
    (h : Fin b → ℕ) (g : Fin c → ℕ) (a : Fin b → Fin c → ℕ → R)
    (x : (Σ i, Fin (g i)) → R) (j : Fin b) (r : Fin (h j)) :
    polynomialHankelAction g a (hankelCoefficientPolynomial g x) j r.val =
      (blockHankel h g a *ᵥ x) ⟨j,r⟩ := by
  simp only [polynomialHankelAction, hankelCoefficientPolynomial_coeff,
    Matrix.mulVec, dotProduct, Fintype.sum_sigma, blockHankel]

def hankelPowerColumn {b : ℕ} (h : Fin b → ℕ) (z : R) (l : Fin b) :
    (Σ j, Fin (h j)) → R :=
  fun jr => if jr.1=l then z^jr.2.val else 0

def hankelInversePolynomial {b c : ℕ} (h : Fin b → ℕ) (g : Fin c → ℕ)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R) (z : R) (l : Fin b) :
    Fin c → R[X] :=
  hankelCoefficientPolynomial g (B *ᵥ hankelPowerColumn h z l)

theorem hankelInversePolynomial_action {b c : ℕ} (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a * B = 1) (z : R) (l j : Fin b) (r : Fin (h j)) :
    polynomialHankelAction g a (hankelInversePolynomial h g B z l) j r.val =
      if j=l then z^r.val else 0 := by
  rw [hankelInversePolynomial, hankelCoefficientPolynomial_action,
    Matrix.mulVec_mulVec, hB, Matrix.one_mulVec]
  rfl

theorem hankelInversePolynomial_shift_zero {b c : ℕ}
    (h : Fin b → ℕ) (g : Fin c → ℕ) (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a * B = 1) (z : R) (l j : Fin b) (r : ℕ)
    (hr : r+1 < h j) :
    polynomialHankelAction (fun i => g i+1) a
      (fun i => (X-C z)*hankelInversePolynomial h g B z l i) j r = 0 := by
  rw [polynomialHankelAction_shift g a (hankelInversePolynomial h g B z l) z
    (hankelCoefficientPolynomial_top_coeff g (B *ᵥ hankelPowerColumn h z l)) j r]
  have h0 := hankelInversePolynomial_action h g a B hB z l j
    (⟨r,by omega⟩ : Fin (h j))
  have h1 := hankelInversePolynomial_action h g a B hB z l j
    (⟨r+1,hr⟩ : Fin (h j))
  dsimp only at h0 h1
  rw [h0,h1]
  by_cases hj : j=l
  · simp [hj, pow_succ, mul_comm]
  · simp [hj]

end FD56
