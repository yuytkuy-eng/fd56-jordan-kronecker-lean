/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicRowExtension

/-! Scalar obstruction induction for a completion of arbitrary finite rank. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K m r q : Type*} [Field K] [Fintype m] [Fintype r] [Fintype q]
  [DecidableEq m] [DecidableEq r] [DecidableEq q]

omit [Fintype m] [Fintype r] [Fintype q] [DecidableEq m] [DecidableEq r] [DecidableEq q] in
theorem cubic_scalar_jet_zero (Q Z W : Matrix q q K[X]) (c : K[X])
    (hQ : DegreeBound Q 1) (hrel : Q=(X^3 : K[X]) • Z+c • W)
    (hjet : Function.Injective (Matrix.mulVec
      (fun (ij : q × q) (k : Fin 3) => (W ij.1 ij.2).coeff (2-k.val)))) :
    ∀ k<3, c.coeff k=0 := by
  have hvec : (fun (ij : q × q) (k : Fin 3) => (W ij.1 ij.2).coeff (2-k.val)) *ᵥ
      (fun k : Fin 3 => c.coeff k.val)=0 := by
    funext ij
    have hz : (Q ij.1 ij.2).coeff 2=0 :=
      coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hQ ij.1 ij.2) (by decide))
    rw [hrel] at hz
    simpa [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul,coeff_add,coeff_X_pow_mul,
      coeff_mul,Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk,Finset.sum_range_succ,
      Fin.sum_univ_succ,Matrix.mulVec,dotProduct,mul_comm,add_assoc,add_left_comm,add_comm] using hz
  have hv : (fun k : Fin 3 => c.coeff k.val)=0 :=
    hjet (by simpa only [Matrix.mulVec_zero] using hvec)
  intro k hk
  exact congrFun hv ⟨k,hk⟩

theorem cubic_scalar_descent_bounded
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1) (alpha : r → ℕ) (d : ℕ)
    (hd : ∀ i, alpha i+1≤d)
    (E : Matrix (q ⊕ r) (q ⊕ m) K[X]) (c c' : K[X])
    (hE : ∀ i x, (E i x).natDegree≤d+3-(Sum.elim (fun _ : q => 1) alpha i+1))
    (hc : c.natDegree≤d+4) (hfactor : c=X^3*c')
    (hrel : E*cubicRowExtension G S=(-c) • 1) :
    ∃ F : Matrix r m K[X],
      (∀ i x, (F i x).natDegree≤d-(alpha i+1)) ∧ c'.natDegree≤d+1 ∧
      F*G=(-c') • 1 := by
  obtain ⟨F,hF,hFG⟩ := cubicRowExtension_scalar_descent G S R V W hcomp E c hrel c' hfactor
  refine ⟨F,?_,?_,hFG⟩
  · intro i x
    apply polynomial_cubic_factor_degree (E (Sum.inr i) (Sum.inr x)) (F i x)
      (d-(alpha i+1))
    · exact congrArg (fun A : Matrix r m K[X] => A i x) hF
    · have hh := hE (Sum.inr i) (Sum.inr x)
      have hi := hd i
      simp only [Sum.elim_inr] at hh
      omega
  · apply polynomial_cubic_factor_degree c c' (d+1) hfactor
    simpa [Nat.add_assoc] using hc

theorem cubic_scalar_zero_extend
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1) (alpha : r → ℕ) (b : ℕ)
    (hd : ∀ i, alpha i+1≤b)
    (hV : DegreeBound V b)
    (hlead : Function.Injective (Matrix.mulVec (fun x j => (V j x).coeff b)))
    (hjet : Function.Injective (Matrix.mulVec
      (fun (ij : q × q) (k : Fin 3) => (W ij.1 ij.2).coeff (2-k.val))))
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]),
      (∀ i x, (E i x).natDegree≤b-(alpha i+1)) → c.natDegree≤b+1 →
      E*G=(-c) • 1 → c=0)
    (E : Matrix (q ⊕ r) (q ⊕ m) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree≤b+3-(Sum.elim (fun _ : q => 1) alpha i+1))
    (hc : c.natDegree≤b+4) (hrel : E*cubicRowExtension G S=(-c) • 1) : c=0 := by
  obtain ⟨Q,hQV,hQ⟩ := cubicRowExtension_new_coordinates G S R V W hcomp E c hrel
  have hsmall : DegreeBound Q 1 := by
    intro i j
    have hh := (polynomial_combination_degree_iff V.transpose (fun _ => b) (Q i) (b+1)
      (fun x j => hV j x) hlead).mp (by
        intro x
        have he := congrArg (fun A : Matrix q m K[X] => A i x) hQV
        change E (Sum.inl i) (Sum.inr x)=(Q*V) i x at he
        have hdE := hE (Sum.inl i) (Sum.inr x)
        simp only [Sum.elim_inl] at hdE
        have hdE' : (E (Sum.inl i) (Sum.inr x)).natDegree≤b+1 := hdE.trans (by omega)
        rw [he] at hdE'
        simpa only [Matrix.mulVec,Matrix.mul_apply,dotProduct,Matrix.transpose_apply,mul_comm] using hdE')
    rcases hh j with hz | ⟨_,hh⟩
    · simp [hz]
    · simpa using hh
  have hform : Q=(X^3 : K[X]) • (E.submatrix Sum.inl Sum.inl*W)+c • W := by
    rw [hQ,Matrix.add_mul,Matrix.smul_mul,Matrix.smul_mul,Matrix.one_mul]
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr
    (cubic_scalar_jet_zero Q _ W c hsmall hform hjet)
  obtain ⟨F,hF,hc',hFG⟩ := cubic_scalar_descent_bounded G S R V W hcomp alpha b hd
    E c c' hE hc hfactor hrel
  rw [hfactor,hzero F c' hF hc' hFG,mul_zero]

theorem cubic_scalar_selector_extend {t : Type*}
    (G : Matrix m r K[X]) (S : Matrix m q K[X])
    (R : Matrix r m K[X]) (V : Matrix q m K[X]) (W : Matrix q q K[X])
    (hcomp : G*R+S*W*V=1) (alpha : r → ℕ) (d : ℕ)
    (hd : ∀ i, alpha i+1≤d) (f : t → ℕ)
    (hzero : ∀ (E : Matrix r m K[X]) (c : K[X]),
      (∀ i x, (E i x).natDegree≤d-(alpha i+1)) → c.natDegree≤d+1 →
      E*G=(-c) • 1 → (∀ j, c.coeff (f j)=0) → c=0)
    (E : Matrix (q ⊕ r) (q ⊕ m) K[X]) (c : K[X])
    (hE : ∀ i x, (E i x).natDegree≤d+3-(Sum.elim (fun _ : q => 1) alpha i+1))
    (hc : c.natDegree≤d+4) (hrel : E*cubicRowExtension G S=(-c) • 1)
    (hsel : ∀ j : Fin 3 ⊕ t,
      c.coeff (Sum.elim (fun k : Fin 3 => k.val) (fun j => f j+3) j)=0) : c=0 := by
  have hlow : ∀ k<3, c.coeff k=0 := fun k hk => hsel (Sum.inl ⟨k,hk⟩)
  obtain ⟨c',hfactor⟩ := Polynomial.X_pow_dvd_iff.mpr hlow
  obtain ⟨F,hF,hc',hFG⟩ := cubic_scalar_descent_bounded G S R V W hcomp alpha d hd
    E c c' hE hc hfactor hrel
  have hc'zero := hzero F c' hF hc' hFG (by
    intro j
    simpa only [Sum.elim_inr,hfactor,coeff_X_pow_mul] using hsel (Sum.inr j))
  rw [hfactor,hc'zero,mul_zero]

omit [Fintype r] [Fintype q] [DecidableEq m] [DecidableEq r] [DecidableEq q] in
theorem cubic_kernel_degree_of_constant_selector
    (V : Matrix q m K[X]) (S : Matrix m q K[X]) (b : ℕ)
    (hV : DegreeBound V b) (hS : DegreeBound S 0) :
    DegreeBound (cubicRowExtensionKernel V S) (b+3) := by
  intro i x
  cases x with
  | inl x =>
    have hh := degreeBound_mul hV hS i x
    exact hh.trans (by omega)
  | inr x =>
    change (X^3*V i x).natDegree≤b+3
    apply natDegree_mul_le.trans
    have hh := hV i x
    simp only [natDegree_X_pow]
    omega

end FD56
