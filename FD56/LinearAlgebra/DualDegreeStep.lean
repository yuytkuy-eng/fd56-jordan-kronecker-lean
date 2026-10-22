/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialMatrix
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Elementary polynomial row operations raise prescribed minimal degrees. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a r : Type*} [Field K] [DecidableEq a] [DecidableEq r]

def raisedDegree (e : r → ℕ) (j : r) : r → ℕ := Function.update e j (e j + 1)

def polynomialRowShear (F : Matrix a r K[X]) (u v : a) (σ : K) : Matrix a r K[X] :=
  fun x k => F x k + if x = v then C σ * (X * F u k) else 0

theorem shifted_polynomial_degree_le (p : K[X]) (e : ℕ) (σ : K)
    (hp : p.natDegree ≤ e) : (C σ * (X * p)).natDegree ≤ e + 1 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  cases N with
  | zero => omega
  | succ N =>
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))]
    simp

theorem shifted_polynomial_degree_le_of_top_zero (p : K[X]) (e : ℕ) (σ : K)
    (hp : p.natDegree ≤ e) (hz : p.coeff e = 0) :
    (C σ * (X * p)).natDegree ≤ e := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro N hN
  cases N with
  | zero => omega
  | succ N =>
    rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_mul]
    by_cases he : N = e
    · simp [he, hz]
    · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hp (by omega))]
      simp

theorem polynomialRowShear_degree (F : Matrix a r K[X]) (e : r → ℕ)
    (p : r → a) (hp : Function.Injective p) (j : r) (v : a) (σ : K)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hL : ∀ x k, (F x k).coeff (e k) = if x = p k then 1 else 0) :
    ∀ x k, (polynomialRowShear F (p j) v σ x k).natDegree ≤ raisedDegree e j k := by
  intro x k
  unfold polynomialRowShear
  apply Polynomial.natDegree_add_le_of_degree_le
  · by_cases hk : k = j
    · subst k; simpa [raisedDegree] using (hF x j).trans (Nat.le_succ (e j))
    · simpa [raisedDegree, hk] using hF x k
  · split_ifs
    · by_cases hk : k = j
      · subst k
        simpa [raisedDegree] using shifted_polynomial_degree_le (F (p j) j) (e j) σ (hF _ _)
      · have hz : (F (p j) k).coeff (e k) = 0 := by
          rw [hL]; simp [show p j ≠ p k from fun h => hk (hp h).symm]
        simpa [raisedDegree, hk] using
          shifted_polynomial_degree_le_of_top_zero (F (p j) k) (e k) σ (hF _ _) hz
    · simp

theorem polynomialRowShear_lead_pivot (F : Matrix a r K[X]) (e : r → ℕ)
    (p : r → a) (hp : Function.Injective p) (j : r) (v : a) (σ : K)
    (hv : ∀ k, p k ≠ v)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hL : ∀ x k, (F x k).coeff (e k) = if x = p k then 1 else 0)
    (k : r) (hk : k ≠ j) (l : r) :
    (polynomialRowShear F (p j) v σ (p k) l).coeff (raisedDegree e j l) =
      if k = l then 1 else 0 := by
  simp only [polynomialRowShear, if_neg (hv k), add_zero]
  by_cases hl : l = j
  · subst l
    rw [show raisedDegree e j j = e j + 1 by simp [raisedDegree]]
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt ((hF (p k) j).trans_lt (Nat.lt_succ_self _))]
    simp [hk]
  · rw [show raisedDegree e j l = e l by simp [raisedDegree, hl], hL]
    simp [hp.eq_iff]

theorem polynomialRowShear_lead_selected (F : Matrix a r K[X]) (e : r → ℕ)
    (p : r → a) (j : r) (v : a) (σ : K)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hL : ∀ x k, (F x k).coeff (e k) = if x = p k then 1 else 0) :
    (polynomialRowShear F (p j) v σ v j).coeff (raisedDegree e j j) = σ := by
  have hz : (F v j).coeff (e j + 1) = 0 :=
    Polynomial.coeff_eq_zero_of_natDegree_lt ((hF v j).trans_lt (Nat.lt_succ_self _))
  simp [polynomialRowShear, raisedDegree, Polynomial.coeff_add,
    Polynomial.coeff_C_mul, Polynomial.coeff_X_mul, hz, hL]

theorem polynomialRowShear_lead_injective [Fintype r]
    (F : Matrix a r K[X]) (e : r → ℕ) (p : r → a) (hp : Function.Injective p)
    (j : r) (v : a) (σ : K) (hσ : σ ≠ 0) (hv : ∀ k, p k ≠ v)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hL : ∀ x k, (F x k).coeff (e k) = if x = p k then 1 else 0) :
    Function.Injective (Matrix.mulVec (fun x k =>
      (polynomialRowShear F (p j) v σ x k).coeff (raisedDegree e j k))) := by
  let A : Matrix a r K := fun x k =>
    (polynomialRowShear F (p j) v σ x k).coeff (raisedDegree e j k)
  intro b c hbc
  have hz : A *ᵥ (b - c) = 0 := by rw [Matrix.mulVec_sub, hbc, sub_self]
  have ho (k : r) (hk : k ≠ j) : (b - c) k = 0 := by
    have hh := congrArg (fun w => w (p k)) hz
    have hrow : ∀ l, A (p k) l = if k = l then 1 else 0 :=
      polynomialRowShear_lead_pivot F e p hp j v σ hv hF hL k hk
    simpa [Matrix.mulVec, dotProduct, hrow] using hh
  have hj : (b - c) j = 0 := by
    have hh := congrArg (fun w => w v) hz
    have hs : ∑ k, A v k * (b - c) k = A v j * (b - c) j := by
      apply Finset.sum_eq_single j
      · intro k _ hk; rw [ho k hk, mul_zero]
      · simp
    change (∑ k, A v k * (b - c) k) = 0 at hh
    rw [hs] at hh
    have ha : A v j = σ := polynomialRowShear_lead_selected F e p j v σ hF hL
    rw [ha] at hh
    exact (mul_eq_zero.mp hh).resolve_left hσ
  funext k
  exact sub_eq_zero.mp (if hk : k = j then by simpa [hk] using hj else ho k hk)

theorem polynomialRowShear_exact_degree (F : Matrix a r K[X]) (e : r → ℕ)
    (p : r → a) (hp : Function.Injective p) (j : r) (v : a) (σ : K)
    (hσ : σ ≠ 0) (hv : ∀ k, p k ≠ v)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hL : ∀ x k, (F x k).coeff (e k) = if x = p k then 1 else 0) :
    ∀ k, ∃ x, (polynomialRowShear F (p j) v σ x k).natDegree = raisedDegree e j k := by
  intro k
  have hb := polynomialRowShear_degree F e p hp j v σ hF hL
  by_cases hk : k = j
  · subst k
    refine ⟨v, le_antisymm (hb v j) (Polynomial.le_natDegree_of_ne_zero ?_)⟩
    rwa [polynomialRowShear_lead_selected F e p j v σ hF hL]
  · refine ⟨p k, le_antisymm (hb (p k) k) (Polynomial.le_natDegree_of_ne_zero ?_)⟩
    rw [polynomialRowShear_lead_pivot F e p hp j v σ hv hF hL k hk k]
    simp

omit [DecidableEq r] in
theorem polynomialRowShear_eq_transvection_mul [Fintype a]
    (F : Matrix a r K[X]) (u v : a) (σ : K) :
    polynomialRowShear F u v σ = Matrix.transvection v u (C σ * X) * F := by
  ext x k
  by_cases hx : x = v
  · subst x
    simp [polynomialRowShear, Matrix.transvection, Matrix.add_mul, mul_assoc]
  · simp [polynomialRowShear, Matrix.transvection, Matrix.add_mul, hx]

omit [DecidableEq r] in
theorem polynomialRowShear_transpose_eq_mul_transvection [Fintype a]
    (T : Matrix r a K[X]) (u v : a) (σ : K) :
    (polynomialRowShear T.transpose v u (-σ)).transpose =
      T * Matrix.transvection v u (-(C σ * X)) := by
  apply Matrix.ext
  intro k x
  by_cases hx : x = u
  · subst x
    simp only [polynomialRowShear, Matrix.transpose_apply, if_pos rfl, map_neg,
      neg_mul, Matrix.transvection, Matrix.mul_add, Matrix.mul_one, Matrix.add_apply,
      Matrix.StdBasisMatrix.mul_right_apply_same]
    simp only [ite_true]
    ring
  · simp [polynomialRowShear, Matrix.transvection, Matrix.mul_add, hx]

theorem polynomial_shear_inverse [Fintype a] (u v : a) (huv : u ≠ v) (σ : K) :
    Matrix.transvection v u (C σ * X) * Matrix.transvection v u (-(C σ * X)) =
      (1 : Matrix a a K[X]) ∧
    Matrix.transvection v u (-(C σ * X)) * Matrix.transvection v u (C σ * X) =
      (1 : Matrix a a K[X]) := by
  constructor <;> rw [Matrix.transvection_mul_transvection_same v u huv.symm] <;> simp

omit [DecidableEq r] in
theorem polynomial_dual_shear_product [Fintype a] {s : Type*}
    (F : Matrix a r K[X]) (T : Matrix s a K[X]) (u v : a) (huv : u ≠ v) (σ : K) :
    (polynomialRowShear T.transpose v u (-σ)).transpose * polynomialRowShear F u v σ =
      T * F := by
  rw [polynomialRowShear_transpose_eq_mul_transvection,
    polynomialRowShear_eq_transvection_mul]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc
    (Matrix.transvection v u (-(C σ * X))), (polynomial_shear_inverse u v huv σ).2,
    Matrix.one_mul]

omit [DecidableEq a] [DecidableEq r] in
theorem polynomial_leading_pair_mul_eq_zero [Fintype a] {s : Type*}
    (F : Matrix a r K[X]) (T : Matrix s a K[X]) (e : r → ℕ) (f : s → ℕ)
    (hF : ∀ x k, (F x k).natDegree ≤ e k)
    (hT : ∀ i x, (T i x).natDegree ≤ f i) (hTF : T * F = 0) :
    (show Matrix s a K from fun i x => (T i x).coeff (f i)) *
      (show Matrix a r K from fun x k => (F x k).coeff (e k)) = 0 := by
  ext i k
  have h := congrArg (fun A : Matrix s r K[X] => (A i k).coeff (f i + e k)) hTF
  change ((T * F) i k).coeff (f i + e k) = 0 at h
  have hm : ((T * F) i k).coeff (f i + e k) =
      ∑ x, (T i x).coeff (f i) * (F x k).coeff (e k) := by
    rw [Matrix.mul_apply, Polynomial.finset_sum_coeff]
    apply Finset.sum_congr rfl
    intro x _
    exact Polynomial.coeff_mul_add_eq_of_natDegree_le (hT i x) (hF x k)
  rw [hm] at h
  exact h

end FD56
