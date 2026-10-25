/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AffineKernelCoefficientGap
import FD56.LinearAlgebra.PredictableDegree

/-! Coefficients of independent kernel chains of the same minimal degree are independent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K]

def uniformReversePolynomial (e : ℕ) (c : Fin (e + 1) → K) : K[X] :=
  ∑ k, Polynomial.monomial (e - k.val) (c k)

theorem uniformReversePolynomial_natDegree (e : ℕ) (c : Fin (e + 1) → K) :
    (uniformReversePolynomial e c).natDegree ≤ e := by
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k _
  exact (Polynomial.natDegree_monomial_le _).trans (Nat.sub_le _ _)

theorem uniformReversePolynomial_coeff (e : ℕ) (c : Fin (e + 1) → K)
    (k : Fin (e + 1)) : (uniformReversePolynomial e c).coeff (e - k.val) = c k := by
  classical
  have hi (l : Fin (e + 1)) : e - l.val = e - k.val ↔ l = k := by
    constructor
    · intro h
      apply Fin.ext
      have hl := l.isLt
      have hk := k.isLt
      omega
    · rintro rfl
      rfl
  simp only [uniformReversePolynomial, Polynomial.finset_sum_coeff, Polynomial.coeff_monomial,
    hi, Finset.sum_ite_eq', Finset.mem_univ, if_true]

variable {a b j : Type*} [Fintype b] [Fintype j]

omit [Fintype b] in
theorem uniform_kernel_combination_middle_coefficient (V : Matrix b j K[X])
    (e : ℕ) (c : j × Fin (e + 1) → K) (i : b) :
    ((V *ᵥ fun j => uniformReversePolynomial e (fun k => c (j,k))) i).coeff e =
      ((fun i jk => (V i jk.1).coeff jk.2.val) *ᵥ c) i := by
  simp only [Matrix.mulVec, dotProduct, uniformReversePolynomial, Finset.mul_sum,
    Polynomial.finset_sum_coeff, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  have he : k.val + (e - k.val) = e := by omega
  simpa only [he] using Polynomial.coeff_mul_monomial (V i j) (e - k.val) k.val (c (j,k))

theorem uniform_kernel_coefficients_injective (A B : Matrix a b K)
    (V : Matrix b j K[X]) (e : ℕ)
    (hAV : affineMatrixPencil A B * V = 0)
    (hV : Function.Injective V.mulVec)
    (hdegree : ∀ i j, (V i j).natDegree ≤ e)
    (hshort : ∀ w : b → K[X], affineMatrixPencil A B *ᵥ w = 0 →
      (∀ i, (w i).natDegree < e) → w = 0) :
    Function.Injective (Matrix.mulVec (fun i (jk : j × Fin (e + 1)) =>
      (V i jk.1).coeff jk.2.val)) := by
  have hz (c : j × Fin (e + 1) → K)
      (hc : (fun i jk => (V i jk.1).coeff jk.2.val) *ᵥ c = 0) : c = 0 := by
    let p : j → K[X] := fun j => uniformReversePolynomial e (fun k => c (j,k))
    let h : b → K[X] := V *ᵥ p
    have hh : affineMatrixPencil A B *ᵥ h = 0 := by
      dsimp only [h]
      rw [Matrix.mulVec_mulVec, hAV, Matrix.zero_mulVec]
    have hd : ∀ i, (h i).natDegree ≤ 2 * e := by
      apply polynomial_combination_degree_bound V (fun _ => e) p (2 * e) hdegree
      intro j
      refine Or.inr ⟨by omega, ?_⟩
      have hp := uniformReversePolynomial_natDegree e (fun k => c (j,k))
      change (uniformReversePolynomial e (fun k => c (j,k))).natDegree ≤ 2 * e - e
      omega
    have hg : ∀ i, (h i).coeff e = 0 := by
      intro i
      exact (uniform_kernel_combination_middle_coefficient V e c i).trans (congrFun hc i)
    have hhzero : h = 0 := by
      by_cases he : 0 < e
      · exact affine_kernel_zero_of_middle_coefficient_gap A B e he hshort h hh hd hg
      · have he : e = 0 := by omega
        subst e
        funext i
        apply Polynomial.ext
        intro k
        simp only [Pi.zero_apply, Polynomial.coeff_zero]
        cases k with
        | zero => exact hg i
        | succ k =>
          apply Polynomial.coeff_eq_zero_of_natDegree_lt
          have := hd i
          omega
    have hpzero : p = 0 := hV (by
      change h = V *ᵥ 0
      rw [hhzero, Matrix.mulVec_zero])
    funext jk
    have he := congrArg (fun f : K[X] => f.coeff (e - jk.2.val)) (congrFun hpzero jk.1)
    simpa only [p, uniformReversePolynomial_coeff, Pi.zero_apply, Polynomial.coeff_zero] using he
  intro x y hxy
  have h := hz (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

end FD56
