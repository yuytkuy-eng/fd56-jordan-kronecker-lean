/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.UniformKernelCoefficients

/-! Images of the noninitial coefficients of minimal uniform kernel chains are independent. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b j : Type*} [Field K] [Fintype b] [Fintype j]

theorem polynomialTail_natDegree_lt_of_positive_shift (p : K[X]) (e s : ℕ)
    (he : 0 < e) (hs : 0 < s) (hp : p.natDegree ≤ e) :
    (polynomialTail s p).natDegree < e := by
  apply Nat.lt_of_le_pred he
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [polynomialTail_coeff]
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simp only [Nat.pred_eq_sub_one] at hk
  omega

theorem uniform_kernel_functionals_injective (A B : Matrix a b K)
    (V : Matrix b j K[X]) (e : ℕ)
    (hAV : affineMatrixPencil A B * V = 0)
    (hdegree : ∀ i j, (V i j).natDegree ≤ e)
    (hshort : ∀ w : b → K[X], affineMatrixPencil A B *ᵥ w = 0 →
      (∀ i, (w i).natDegree < e) → w = 0)
    (hcoeff : Function.Injective (Matrix.mulVec (fun i (jk : j × Fin (e + 1)) =>
      (V i jk.1).coeff jk.2.val))) :
    Function.Injective (Matrix.mulVec (fun i (jk : j × Fin e) =>
      (A *ᵥ fun x => (V x jk.1).coeff (jk.2.val + 1)) i)) := by
  classical
  by_cases he : 0 < e
  swap
  · have he : e = 0 := by omega
    subst e
    exact fun _ _ _ => Subsingleton.elim _ _
  have hcol (l : j) : affineMatrixPencil A B *ᵥ (fun i => V i l) = 0 := by
    funext i
    exact congrFun (congrFun hAV i) l
  have hz (c : j × Fin e → K)
      (hc : (fun i (jk : j × Fin e) =>
        (A *ᵥ fun x => (V x jk.1).coeff (jk.2.val + 1)) i) *ᵥ c = 0) : c = 0 := by
    let u : b → K[X] := fun i =>
      ∑ jk : j × Fin e, Polynomial.C (c jk) * polynomialTail (jk.2.val + 1) (V i jk.1)
    have hucoeff (i : b) (k : ℕ) :
        (u i).coeff k = ∑ jk : j × Fin e, c jk * (V i jk.1).coeff (k + (jk.2.val + 1)) := by
      simp only [u, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul, polynomialTail_coeff]
    have hudeg : ∀ i, (u i).natDegree < e := by
      intro i
      apply Nat.lt_of_le_pred he
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro jk _
      have htail := polynomialTail_natDegree_lt_of_positive_shift (V i jk.1) e
        (jk.2.val + 1) he (by omega) (hdegree i jk.1)
      have hmul := Polynomial.natDegree_mul_le (p := Polynomial.C (c jk))
        (q := polynomialTail (jk.2.val + 1) (V i jk.1))
      simp only [Polynomial.natDegree_C, zero_add] at hmul
      simp only [Nat.pred_eq_sub_one]
      omega
    have huker : affineMatrixPencil A B *ᵥ u = 0 := by
      funext i
      apply Polynomial.ext
      intro k
      simp only [Pi.zero_apply, Polynomial.coeff_zero]
      cases k with
      | zero =>
        rw [affineMatrixPencil_mulVec_coeff_zero]
        have h := congrFun hc i
        simp only [Matrix.mulVec, dotProduct, hucoeff, zero_add, Finset.mul_sum] at h ⊢
        rw [Finset.sum_comm]
        simp only [Finset.sum_mul] at h
        simpa only [mul_assoc, mul_comm, mul_left_comm, Pi.zero_apply] using h
      | succ k =>
        rw [affineMatrixPencil_mulVec_coeff_succ]
        simp only [Matrix.mulVec, dotProduct, hucoeff, Finset.mul_sum]
        rw [Finset.sum_comm (f := fun x (jk : j × Fin e) =>
          A i x * (c jk * (V x jk.1).coeff ((k + 1) + (jk.2.val + 1)))),
          Finset.sum_comm (f := fun x (jk : j × Fin e) =>
          B i x * (c jk * (V x jk.1).coeff (k + (jk.2.val + 1))))]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_eq_zero
        intro jk _
        have h := congrArg (fun z : a → K[X] => (z i).coeff ((k + (jk.2.val + 1)) + 1))
          (hcol jk.1)
        dsimp only at h
        rw [affineMatrixPencil_mulVec_coeff_succ] at h
        simp only [Matrix.mulVec, dotProduct,
          Pi.zero_apply, Polynomial.coeff_zero] at h
        have hmul := congrArg (fun x : K => c jk * x) h
        simpa only [mul_add, Finset.mul_sum, mul_assoc, mul_comm, mul_left_comm,
          Nat.add_right_comm k 1 (jk.2.val + 1), mul_zero] using hmul
    have huzero := hshort u huker hudeg
    let c' : j × Fin (e + 1) → K := fun jk => Fin.cases 0 (fun k => c (jk.1,k)) jk.2
    have hc' : c' = 0 := by
      apply hcoeff
      rw [Matrix.mulVec_zero]
      funext i
      have h := congrArg (fun p : K[X] => p.coeff 0) (congrFun huzero i)
      simp only [hucoeff, zero_add, Pi.zero_apply, Polynomial.coeff_zero] at h
      simpa only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, Fin.sum_univ_succ,
        c', Fin.cases_zero, Fin.cases_succ, mul_zero, zero_mul, zero_add, Fin.val_succ,
        mul_comm, Pi.zero_apply] using h
    funext jk
    exact congrFun hc' (jk.1,jk.2.succ)
  intro x y hxy
  have h := hz (x - y) (by rw [Matrix.mulVec_sub, hxy, sub_self])
  exact sub_eq_zero.mp h

end FD56
