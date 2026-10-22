/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualDegreeStep
import FD56.LinearAlgebra.DualStepPair
import FD56.LinearAlgebra.DualConstant
import FD56.LinearAlgebra.DualBasis

/-! Constructing dual polynomial bases with prescribed degree lists. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {r s : Type*} [Fintype r] [Fintype s] [DecidableEq r] [DecidableEq s]

def HasNormalizedDualPair (K : Type*) [Field K] (e : r → ℕ) (f : s → ℕ) : Prop :=
  ∃ U V : Matrix (r ⊕ s) (r ⊕ s) K[X],
    U * V = 1 ∧ V * U = 1 ∧
    (∀ x j, (U x (Sum.inl j)).natDegree ≤ e j) ∧
    (∀ i x, (V (Sum.inr i) x).natDegree ≤ f i) ∧
    (∀ x j, (U x (Sum.inl j)).coeff (e j) = if x = Sum.inl j then 1 else 0) ∧
    (∀ i x, (V (Sum.inr i) x).coeff (f i) = if x = Sum.inr i then 1 else 0)

theorem normalizedDualPair_zero (K : Type*) [Field K] :
    HasNormalizedDualPair K (0 : r → ℕ) (0 : s → ℕ) := by
  refine ⟨1, 1, by simp, by simp, ?_, ?_, ?_, ?_⟩
  · intro x j; by_cases h : x = Sum.inl j <;> simp [Matrix.one_apply, h]
  · intro i x; by_cases h : Sum.inr i = x <;> simp [Matrix.one_apply, h]
  · intro x j; by_cases h : x = Sum.inl j <;> simp [Matrix.one_apply, h]
  · intro i x; by_cases h : x = Sum.inr i <;> simp [Matrix.one_apply, h, eq_comm]

theorem normalizedDualPair_of_reduced {K : Type*} [Field K]
    (U V : Matrix (r ⊕ s) (r ⊕ s) K[X]) (e : r → ℕ) (f : s → ℕ)
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hU : ∀ x j, (U x (Sum.inl j)).natDegree ≤ e j)
    (hV : ∀ i x, (V (Sum.inr i) x).natDegree ≤ f i)
    (hUL : Function.Injective (Matrix.mulVec
      (show Matrix (r ⊕ s) r K from fun x j => (U x (Sum.inl j)).coeff (e j))))
    (hVL : Function.Injective (Matrix.mulVec
      (show Matrix (r ⊕ s) s K from fun x i => (V (Sum.inr i) x).coeff (f i)))) :
    HasNormalizedDualPair K e f := by
  let F := U.submatrix id Sum.inl
  let T := V.submatrix Sum.inr id
  let A : Matrix (r ⊕ s) r K := fun x j => (F x j).coeff (e j)
  let B : Matrix s (r ⊕ s) K := fun i x => (T i x).coeff (f i)
  have hBA : B * A = 0 := polynomial_leading_pair_mul_eq_zero F T e f hU hV
    (inversePair_rightRows_mul_leftColumns U V hVU)
  obtain ⟨H, J, hHJ, hJH, hJA, hBH, _⟩ := exists_dual_matrix_normalization A B hBA hUL
    (matrix_surjective_of_transpose_injective B hVL)
  obtain ⟨hF, hT, hFL, hTL⟩ := dual_constant_normalization F T e f H J hU hV hJA hBH
  have hHJp : H.map Polynomial.C * J.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hHJ, Matrix.map_one] <;> simp
  have hJHp : J.map Polynomial.C * H.map Polynomial.C = 1 := by
    rw [← Matrix.map_mul, hJH, Matrix.map_one] <;> simp
  refine ⟨J.map Polynomial.C * U, V * H.map Polynomial.C, ?_, ?_, hF, hT, ?_, ?_⟩
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc U, hUV, Matrix.one_mul, hJHp]
  · rw [Matrix.mul_assoc, ← Matrix.mul_assoc (H.map Polynomial.C), hHJp,
      Matrix.one_mul, hVU]
  · intro x j
    have h := congrArg (fun L : Matrix (r ⊕ s) r K => L x j) hFL
    change ((J.map Polynomial.C * U) x (Sum.inl j)).coeff (e j) = _ at h
    rw [h]
    cases x <;> simp [Matrix.fromRows, Matrix.one_apply]
  · intro i x
    have h := congrArg (fun L : Matrix s (r ⊕ s) K => L i x) hTL
    change ((V * H.map Polynomial.C) (Sum.inr i) x).coeff (f i) = _ at h
    rw [h]
    cases x <;> simp [Matrix.fromCols, Matrix.one_apply, eq_comm]

theorem normalizedDualPair_raise {K : Type*} [Field K]
    (e : r → ℕ) (f : s → ℕ) (j : r) (i : s) (h : HasNormalizedDualPair K e f) :
    HasNormalizedDualPair K (raisedDegree e j) (raisedDegree f i) := by
  obtain ⟨U, V, hUV, hVU, hU, hV, hLU, hLV⟩ := h
  obtain ⟨hUV', hVU', hU', hV', hLU', hLV'⟩ :=
    dual_degree_raise_inverse_pair U V e f j i hUV hVU hU hV hLU hLV
  exact normalizedDualPair_of_reduced _ _ _ _ hUV' hVU' hU' hV' hLU' hLV'

theorem degree_pair_induction
    (P : (r → ℕ) → (s → ℕ) → Prop) (hzero : P 0 0)
    (hstep : ∀ e f j i, P e f → P (raisedDegree e j) (raisedDegree f i))
    (e : r → ℕ) (f : s → ℕ) (hsum : ∑ j, e j = ∑ i, f i) : P e f := by
  classical
  suffices ∀ d, ∀ e : r → ℕ, ∀ f : s → ℕ,
      (∑ j, e j) = d → (∑ i, f i) = d → P e f from
    this _ e f rfl hsum.symm
  intro d
  induction d with
  | zero =>
    intro e f he hf
    have he0 : e = 0 := by
      funext j
      exact (Finset.sum_eq_zero_iff.mp he) j (Finset.mem_univ j)
    have hf0 : f = 0 := by
      funext i
      exact (Finset.sum_eq_zero_iff.mp hf) i (Finset.mem_univ i)
    simpa [he0, hf0] using hzero
  | succ d ih =>
    intro e f he hf
    obtain ⟨j, _, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show ∑ j, e j ≠ 0 by omega)
    obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (show ∑ i, f i ≠ 0 by omega)
    let e' := Function.update e j (e j - 1)
    let f' := Function.update f i (f i - 1)
    have hes : ∑ k, e' k = d := by
      have h₁ := Finset.sum_erase_add Finset.univ e (Finset.mem_univ j)
      have h₂ : ∑ k, e' k = ∑ k ∈ Finset.univ.erase j, e k + (e j - 1) := by
        simp only [e', Finset.sum_update_of_mem (Finset.mem_univ j), Finset.sdiff_singleton_eq_erase, add_comm]
      omega
    have hfs : ∑ k, f' k = d := by
      have h₁ := Finset.sum_erase_add Finset.univ f (Finset.mem_univ i)
      have h₂ : ∑ k, f' k = ∑ k ∈ Finset.univ.erase i, f k + (f i - 1) := by
        simp only [f', Finset.sum_update_of_mem (Finset.mem_univ i), Finset.sdiff_singleton_eq_erase, add_comm]
      omega
    have her : raisedDegree e' j = e := by
      funext k
      by_cases hk : k = j
      · subst k
        simp only [raisedDegree, e', Function.update_self]
        omega
      · simp [raisedDegree, e', hk]
    have hfr : raisedDegree f' i = f := by
      funext k
      by_cases hk : k = i
      · subst k
        simp only [raisedDegree, f', Function.update_self]
        omega
      · simp [raisedDegree, f', hk]
    simpa [her, hfr] using hstep e' f' j i (ih e' f' hes hfs)

theorem exists_normalized_dual_pair (K : Type*) [Field K]
    (e : r → ℕ) (f : s → ℕ) (hsum : ∑ j, e j = ∑ i, f i) :
    HasNormalizedDualPair K e f :=
  degree_pair_induction (HasNormalizedDualPair K) (normalizedDualPair_zero K)
    (normalizedDualPair_raise (K := K)) e f hsum

end FD56
