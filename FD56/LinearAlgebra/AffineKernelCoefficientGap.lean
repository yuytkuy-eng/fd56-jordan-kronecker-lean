/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRows

/-! A zero coefficient separates a polynomial kernel vector of an affine pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a b : Type*} [Field K] [Fintype b]

def polynomialPrefix (e : ℕ) (p : K[X]) : K[X] := by
  classical
  exact Polynomial.ofFn e (fun k => p.coeff k)

theorem polynomialPrefix_coeff (e : ℕ) (p : K[X]) (k : ℕ) :
    (polynomialPrefix e p).coeff k = if k < e then p.coeff k else 0 := by
  classical
  by_cases hk : k < e
  · simp [polynomialPrefix, hk]
  · simp [polynomialPrefix, hk, Nat.le_of_not_gt hk]

theorem affineMatrixPencil_mulVec_coeff_zero (A B : Matrix a b K) (v : b → K[X])
    (i : a) :
    ((affineMatrixPencil A B *ᵥ v) i).coeff 0 =
      (A *ᵥ fun j => (v j).coeff 0) i := by
  simp [affineMatrixPencil, Matrix.mulVec, dotProduct, add_mul, mul_assoc]

theorem affineMatrixPencil_mulVec_coeff_succ (A B : Matrix a b K) (v : b → K[X])
    (i : a) (k : ℕ) :
    ((affineMatrixPencil A B *ᵥ v) i).coeff (k + 1) =
      (A *ᵥ fun j => (v j).coeff (k + 1)) i +
        (B *ᵥ fun j => (v j).coeff k) i := by
  simp [affineMatrixPencil, Matrix.mulVec, dotProduct, add_mul, mul_assoc,
    Polynomial.coeff_X_mul, Finset.sum_add_distrib]

theorem affine_kernel_prefix_of_coefficient_zero (A B : Matrix a b K)
    (v : b → K[X]) (e : ℕ) (hv : affineMatrixPencil A B *ᵥ v = 0)
    (he : ∀ j, (v j).coeff e = 0) :
    affineMatrixPencil A B *ᵥ (fun j => polynomialPrefix e (v j)) = 0 := by
  funext i
  apply Polynomial.ext
  intro k
  simp only [Pi.zero_apply, Polynomial.coeff_zero]
  cases k with
  | zero =>
    rw [affineMatrixPencil_mulVec_coeff_zero]
    by_cases hp : 0 < e
    · simp only [polynomialPrefix_coeff, hp, if_true]
      have h := congrArg (fun w : a → K[X] => (w i).coeff 0) hv
      simpa only [affineMatrixPencil_mulVec_coeff_zero, Pi.zero_apply,
        Polynomial.coeff_zero] using h
    · simp [polynomialPrefix_coeff, hp, Matrix.mulVec, dotProduct]
  | succ k =>
    rw [affineMatrixPencil_mulVec_coeff_succ]
    by_cases hk : k + 1 < e
    · have hk' : k < e := by omega
      simp only [polynomialPrefix_coeff, hk, hk', if_true]
      have h := congrArg (fun w : a → K[X] => (w i).coeff (k + 1)) hv
      simpa only [affineMatrixPencil_mulVec_coeff_succ, Pi.zero_apply,
        Polynomial.coeff_zero] using h
    · by_cases heq : k + 1 = e
      · have hk' : k < e := by omega
        simp only [polynomialPrefix_coeff, hk, hk', if_true, if_false,
          Matrix.mulVec_zero, Pi.zero_apply, zero_add]
        have h := congrArg (fun w : a → K[X] => (w i).coeff (k + 1)) hv
        dsimp only at h
        rw [affineMatrixPencil_mulVec_coeff_succ] at h
        simpa [heq, he, Matrix.mulVec, dotProduct] using h
      · have hk' : ¬ k < e := by omega
        simp [polynomialPrefix_coeff, hk, hk', Matrix.mulVec, dotProduct]

theorem polynomialPrefix_natDegree_lt (e : ℕ) (he : 0 < e) (p : K[X]) :
    (polynomialPrefix e p).natDegree < e := by
  classical
  exact Polynomial.ofFn_natDegree_lt he _

def polynomialTail (e : ℕ) (p : K[X]) : K[X] := by
  classical
  exact Polynomial.ofFn (p.natDegree + 1) (fun k => p.coeff (k.val + e))

theorem polynomialTail_coeff (e : ℕ) (p : K[X]) (k : ℕ) :
    (polynomialTail e p).coeff k = p.coeff (k + e) := by
  classical
  by_cases hk : k < p.natDegree + 1
  · simp [polynomialTail, hk]
  · have hz : p.coeff (k + e) = 0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    simp [polynomialTail, Nat.le_of_not_gt hk, hz]

theorem polynomial_coefficient_gap_split (e : ℕ) (p : K[X]) (he : p.coeff e = 0) :
    p = polynomialPrefix e p + polynomialTail (e + 1) p * X ^ (e + 1) := by
  apply Polynomial.ext
  intro k
  rw [Polynomial.coeff_add, polynomialPrefix_coeff, Polynomial.coeff_mul_X_pow']
  by_cases hk : k < e
  · simp [hk, show ¬ e + 1 ≤ k by omega]
  · by_cases heq : k = e
    · subst k
      simp [he]
    · have hge : e + 1 ≤ k := by omega
      simp only [hk, if_false, hge, if_true, zero_add, polynomialTail_coeff]
      rw [Nat.sub_add_cancel hge]

theorem affine_kernel_tail_of_coefficient_zero (A B : Matrix a b K)
    (v : b → K[X]) (e : ℕ) (hv : affineMatrixPencil A B *ᵥ v = 0)
    (he : ∀ j, (v j).coeff e = 0) :
    affineMatrixPencil A B *ᵥ (fun j => polynomialTail (e + 1) (v j)) = 0 := by
  funext i
  apply Polynomial.ext
  intro k
  simp only [Pi.zero_apply, Polynomial.coeff_zero]
  cases k with
  | zero =>
    rw [affineMatrixPencil_mulVec_coeff_zero]
    simp only [polynomialTail_coeff, zero_add]
    have h := congrArg (fun w : a → K[X] => (w i).coeff (e + 1)) hv
    dsimp only at h
    rw [affineMatrixPencil_mulVec_coeff_succ] at h
    simpa [he, Matrix.mulVec, dotProduct] using h
  | succ k =>
    rw [affineMatrixPencil_mulVec_coeff_succ]
    simp only [polynomialTail_coeff]
    have h := congrArg (fun w : a → K[X] => (w i).coeff ((k + (e + 1)) + 1)) hv
    dsimp only at h
    rw [affineMatrixPencil_mulVec_coeff_succ] at h
    simpa only [Nat.succ_eq_add_one, Nat.add_right_comm k 1 (e + 1),
      Pi.zero_apply, Polynomial.coeff_zero] using h

theorem polynomialTail_gap_natDegree_lt (e : ℕ) (he : 0 < e) (p : K[X])
    (hp : p.natDegree ≤ 2 * e) : (polynomialTail (e + 1) p).natDegree < e := by
  apply Nat.lt_of_le_pred he
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomialTail_coeff]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simp only [Nat.pred_eq_sub_one] at hk
  omega

theorem affine_kernel_zero_of_middle_coefficient_gap (A B : Matrix a b K)
    (e : ℕ) (he : 0 < e)
    (hshort : ∀ w : b → K[X], affineMatrixPencil A B *ᵥ w = 0 →
      (∀ j, (w j).natDegree < e) → w = 0)
    (v : b → K[X]) (hv : affineMatrixPencil A B *ᵥ v = 0)
    (hdegree : ∀ j, (v j).natDegree ≤ 2 * e)
    (hgap : ∀ j, (v j).coeff e = 0) : v = 0 := by
  have hl := hshort (fun j => polynomialPrefix e (v j))
    (affine_kernel_prefix_of_coefficient_zero A B v e hv hgap)
    (fun j => polynomialPrefix_natDegree_lt e he (v j))
  have hu := hshort (fun j => polynomialTail (e + 1) (v j))
    (affine_kernel_tail_of_coefficient_zero A B v e hv hgap)
    (fun j => polynomialTail_gap_natDegree_lt e he (v j) (hdegree j))
  funext j
  rw [polynomial_coefficient_gap_split e (v j) (hgap j), congrFun hl j, congrFun hu j]
  simp

end FD56
