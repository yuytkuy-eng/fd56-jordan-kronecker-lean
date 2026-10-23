/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ScalarBlockObstruction

/-! Extending a scalar-obstruction witness by separated monomial columns. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b c d : Type*} [Field K]
  [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d]

omit [Fintype b] [DecidableEq a] in
theorem bounded_row_zero_of_scalar_obstruction (G : Matrix a b K[X]) (k : ℕ) (j₀ : b)
    (hzero : ∀ (E : Matrix b a K[X]) (c : K[X]), DegreeBound E k →
      E * G = (-c) • 1 → E = 0 ∧ c = 0)
    (v : a → K[X]) (hv : ∀ x, (v x).natDegree ≤ k)
    (hrel : ∀ j, ∑ x, v x * G x j = 0) : v = 0 := by
  let E : Matrix b a K[X] := fun i x => if i = j₀ then v x else 0
  have hE : DegreeBound E k := by
    intro i x
    by_cases hi : i = j₀ <;> simp [E, hi, hv]
  have hEG : E * G = (- (0 : K[X])) • 1 := by
    funext i j
    by_cases hi : i = j₀ <;> simp [Matrix.mul_apply, E, hi, hrel]
  have hh := (hzero E 0 hE hEG).1
  funext x
  simpa [E] using congrFun (congrFun hh j₀) x

omit [Fintype a] [Fintype b] [Fintype c] [Fintype d]
  [DecidableEq a] [DecidableEq b] [DecidableEq c] [DecidableEq d] in
theorem block_sum_degree (G : Matrix a b K[X]) (H : Matrix c d K[X])
    (q : ℕ) (hG : DegreeBound G q) (hH : DegreeBound H q) :
    DegreeBound (Matrix.fromBlocks G 0 0 H) q := by
  intro i j
  cases i <;> cases j
  · exact hG _ _
  · simp [Matrix.fromBlocks]
  · simp [Matrix.fromBlocks]
  · exact hH _ _

omit [Fintype a] [Fintype c] [DecidableEq a] [DecidableEq b]
  [DecidableEq c] [DecidableEq d] in
theorem block_sum_injective (G : Matrix a b K[X]) (H : Matrix c d K[X])
    (hG : Function.Injective G.mulVec) (hH : Function.Injective H.mulVec) :
    Function.Injective (Matrix.fromBlocks G 0 0 H).mulVec := by
  intro u v huv
  have hu : (fun j => u (Sum.inl j)) = (fun j => v (Sum.inl j)) := by
    apply hG
    funext i
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks] using
      congrFun huv (Sum.inl i)
  have hv : (fun j => u (Sum.inr j)) = (fun j => v (Sum.inr j)) := by
    apply hH
    funext i
    simpa [Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Matrix.fromBlocks] using
      congrFun huv (Sum.inr i)
  funext j
  cases j with
  | inl j => exact congrFun hu j
  | inr j => exact congrFun hv j

omit [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq c] in
theorem block_sum_scalar_obstruction (G : Matrix a b K[X]) (H : Matrix c d K[X])
    (k : ℕ) (j₀ : b)
    (hzero : ∀ (E : Matrix b a K[X]) (p : K[X]), DegreeBound E k →
      E * G = (-p) • 1 → E = 0 ∧ p = 0)
    (hH : ∀ (v : c → K[X]), (∀ x, (v x).natDegree ≤ k) →
      (∀ j, ∑ x, v x * H x j = 0) → v = 0)
    (E : Matrix (b ⊕ d) (a ⊕ c) K[X]) (p : K[X]) (hE : DegreeBound E k)
    (hrel : E * Matrix.fromBlocks G 0 0 H = (-p) • 1) : E = 0 ∧ p = 0 := by
  let E₀ : Matrix b a K[X] := E.submatrix Sum.inl Sum.inl
  have hE₀ : DegreeBound E₀ k := fun i j => hE (Sum.inl i) (Sum.inl j)
  have hrel₀ : E₀ * G = (-p) • 1 := by
    funext i j
    simpa [E₀, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks,
      Matrix.one_apply] using congrFun (congrFun hrel (Sum.inl i)) (Sum.inl j)
  have hp := (hzero E₀ p hE₀ hrel₀).2
  rw [hp, neg_zero, zero_smul] at hrel
  refine ⟨?_, hp⟩
  have hleft (i : b ⊕ d) : (fun x => E i (Sum.inl x)) = 0 := by
    apply bounded_row_zero_of_scalar_obstruction G k j₀ hzero _ (fun x => hE i (Sum.inl x))
    intro j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] using
      congrFun (congrFun hrel i) (Sum.inl j)
  have hright (i : b ⊕ d) : (fun x => E i (Sum.inr x)) = 0 := by
    apply hH _ (fun x => hE i (Sum.inr x))
    intro j
    simpa [Matrix.mul_apply, Fintype.sum_sum_type, Matrix.fromBlocks] using
      congrFun (congrFun hrel i) (Sum.inr j)
  funext i j
  cases j with
  | inl j => exact congrFun (hleft i) j
  | inr j => exact congrFun (hright i) j

def separatedMonomialColumns (d : Type*) [DecidableEq d] (q : ℕ) :
    Matrix (d ⊕ d) d K[X] := fun i j =>
  match i with
  | Sum.inl x => if x = j then 1 else 0
  | Sum.inr x => if x = j then X ^ q else 0

omit [Fintype d] in
theorem separatedMonomialColumns_degree (q : ℕ) :
    DegreeBound (separatedMonomialColumns (K := K) d q) q := by
  intro i j
  cases i <;> simp only [separatedMonomialColumns]
  · split_ifs <;> simp
  · split_ifs <;> simp

theorem separatedMonomialColumns_injective (q : ℕ) :
    Function.Injective (separatedMonomialColumns (K := K) d q).mulVec := by
  intro u v h
  funext j
  simpa [Matrix.mulVec, dotProduct, separatedMonomialColumns] using congrFun h (Sum.inl j)

theorem separatedMonomialColumns_row_zero (k q : ℕ) (hkq : k < q)
    (v : d ⊕ d → K[X]) (hv : ∀ x, (v x).natDegree ≤ k)
    (hrel : ∀ j, ∑ x, v x * separatedMonomialColumns (K := K) d q x j = 0) : v = 0 := by
  have heq (j : d) : v (Sum.inl j) + v (Sum.inr j) * X ^ q = 0 := by
    simpa [Fintype.sum_sum_type, separatedMonomialColumns, mul_ite] using hrel j
  have hr (j : d) : v (Sum.inr j) = 0 := by
    by_contra hn
    have hdeg := congrArg Polynomial.natDegree (eq_neg_of_add_eq_zero_left (heq j))
    rw [Polynomial.natDegree_neg, Polynomial.natDegree_mul_X_pow _ hn] at hdeg
    have := hv (Sum.inl j)
    omega
  funext x
  cases x with
  | inl j => simpa [hr] using heq j
  | inr j => exact hr j

theorem exists_uniform_two_witness_extension (r k q : ℕ) (hr : 3 ≤ r) (hkq : k < q)
    (W : Matrix (Fin 6) (Fin 3) K[X]) (hW : DegreeBound W q)
    (hWi : Function.Injective W.mulVec)
    (hzero : ∀ (E : Matrix (Fin 3) (Fin 6) K[X]) (p : K[X]), DegreeBound E k →
      E * W = (-p) • 1 → E = 0 ∧ p = 0) :
    ∃ G : Matrix (Fin 2 × Fin r) (Fin r) K[X], DegreeBound G q ∧
      Function.Injective G.mulVec ∧
      ∀ (E : Matrix (Fin r) (Fin 2 × Fin r) K[X]) (p : K[X]), DegreeBound E k →
        E * G = (-p) • 1 → E = 0 ∧ p = 0 := by
  let H := separatedMonomialColumns (K := K) (Fin (r - 3)) q
  let T := Matrix.fromBlocks W 0 0 H
  let er : (Fin 2 × Fin r) ≃ (Fin 6 ⊕ (Fin (r - 3) ⊕ Fin (r - 3))) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin]
      omega)
  let ec : Fin r ≃ (Fin 3 ⊕ Fin (r - 3)) :=
    Fintype.equivOfCardEq (by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega)
  have hT : DegreeBound T q := block_sum_degree W H q hW (separatedMonomialColumns_degree q)
  have hTi : Function.Injective T.mulVec :=
    block_sum_injective W H hWi (separatedMonomialColumns_injective q)
  refine ⟨T.submatrix er ec, (fun i j => hT (er i) (ec j)), ?_, ?_⟩
  · intro u v huv
    have hh : (fun j => u (ec.symm j)) = (fun j => v (ec.symm j)) := by
      apply hTi
      funext x
      simpa only [Matrix.submatrix_mulVec_equiv, Function.comp_apply,
        Equiv.apply_symm_apply] using congrFun huv (er.symm x)
    funext j
    simpa only [Equiv.symm_apply_apply] using congrFun hh (ec j)
  · intro E p hE hrel
    let E' := E.submatrix ec.symm er.symm
    have hE' : DegreeBound E' k := fun i j => hE (ec.symm i) (er.symm j)
    have hrel' : E' * T = (-p) • 1 := by
      have hEE : E'.submatrix ec er = E := by
        funext i j
        simp [E']
      rw [← hEE, Matrix.submatrix_mul_equiv] at hrel
      funext i j
      have hh := congrFun (congrFun hrel (ec.symm i)) (ec.symm j)
      simpa only [Matrix.submatrix_apply, Equiv.apply_symm_apply, Matrix.smul_apply,
        Matrix.one_apply, Equiv.symm_apply_eq, Equiv.apply_symm_apply,
        ec.symm.injective.eq_iff] using hh
    obtain ⟨hE0, hp0⟩ := block_sum_scalar_obstruction W H k (0 : Fin 3) hzero
      (separatedMonomialColumns_row_zero k q hkq) E' p hE' hrel'
    refine ⟨?_, hp0⟩
    funext i j
    have hh := congrFun (congrFun hE0 (ec i)) (er j)
    simpa [E'] using hh

end FD56
