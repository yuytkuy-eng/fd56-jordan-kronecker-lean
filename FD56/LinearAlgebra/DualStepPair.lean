/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualDegreeStep

/-! A paired degree increment preserves polynomial inverse matrices. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K r s : Type*} [Field K] [Fintype r] [Fintype s]
  [DecidableEq r] [DecidableEq s]

def dualRaisedLeft (U : Matrix (r ⊕ s) (r ⊕ s) K[X]) (j : r) (i : s) :
    Matrix (r ⊕ s) (r ⊕ s) K[X] :=
  polynomialRowShear U (Sum.inl j) (Sum.inr i) 1

def dualRaisedRight (V : Matrix (r ⊕ s) (r ⊕ s) K[X]) (j : r) (i : s) :
    Matrix (r ⊕ s) (r ⊕ s) K[X] :=
  (polynomialRowShear V.transpose (Sum.inr i) (Sum.inl j) (-1)).transpose

theorem dual_degree_raise_inverse_pair
    (U V : Matrix (r ⊕ s) (r ⊕ s) K[X]) (e : r → ℕ) (f : s → ℕ) (j : r) (i : s)
    (hUV : U * V = 1) (hVU : V * U = 1)
    (hU : ∀ x k, (U x (Sum.inl k)).natDegree ≤ e k)
    (hV : ∀ k x, (V (Sum.inr k) x).natDegree ≤ f k)
    (hLU : ∀ x k, (U x (Sum.inl k)).coeff (e k) = if x = Sum.inl k then 1 else 0)
    (hLV : ∀ k x, (V (Sum.inr k) x).coeff (f k) = if x = Sum.inr k then 1 else 0) :
    dualRaisedLeft U j i * dualRaisedRight V j i = 1 ∧
    dualRaisedRight V j i * dualRaisedLeft U j i = 1 ∧
    (∀ x k, (dualRaisedLeft U j i x (Sum.inl k)).natDegree ≤ raisedDegree e j k) ∧
    (∀ k x, (dualRaisedRight V j i (Sum.inr k) x).natDegree ≤ raisedDegree f i k) ∧
    Function.Injective (Matrix.mulVec (fun x k =>
      (dualRaisedLeft U j i x (Sum.inl k)).coeff (raisedDegree e j k))) ∧
    Function.Injective (Matrix.mulVec (fun x k =>
      (dualRaisedRight V j i (Sum.inr k) x).coeff (raisedDegree f i k))) := by
  let E : Matrix (r ⊕ s) (r ⊕ s) K[X] :=
    Matrix.transvection (Sum.inr i) (Sum.inl j) (C (1 : K) * X)
  let D : Matrix (r ⊕ s) (r ⊕ s) K[X] :=
    Matrix.transvection (Sum.inr i) (Sum.inl j) (-(C (1 : K) * X))
  have hE : E * D = 1 ∧ D * E = 1 :=
    polynomial_shear_inverse (Sum.inl j) (Sum.inr i) (by simp) 1
  have hleft : dualRaisedLeft U j i = E * U :=
    polynomialRowShear_eq_transvection_mul U (Sum.inl j) (Sum.inr i) 1
  have hright : dualRaisedRight V j i = V * D :=
    polynomialRowShear_transpose_eq_mul_transvection V (Sum.inl j) (Sum.inr i) 1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hleft, hright]
    calc
      E * U * (V * D) = E * (U * V) * D := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hUV, Matrix.mul_one, hE.1]
  · rw [hleft, hright]
    calc
      V * D * (E * U) = V * (D * E) * U := by simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hE.2, Matrix.mul_one, hVU]
  · exact polynomialRowShear_degree
      (fun x k => U x (Sum.inl k)) e Sum.inl Sum.inl_injective j (Sum.inr i) 1 hU hLU
  · intro k x
    exact polynomialRowShear_degree
      (fun x k => V (Sum.inr k) x) f Sum.inr Sum.inr_injective i (Sum.inl j) (-1)
      (fun x k => hV k x) (fun x k => hLV k x) x k
  · exact polynomialRowShear_lead_injective
      (fun x k => U x (Sum.inl k)) e Sum.inl Sum.inl_injective j (Sum.inr i) 1
      one_ne_zero (by simp) hU hLU
  · exact polynomialRowShear_lead_injective
      (fun x k => V (Sum.inr k) x) f Sum.inr Sum.inr_injective i (Sum.inl j) (-1)
      (neg_ne_zero.mpr one_ne_zero) (by simp) (fun x k => hV k x) (fun x k => hLV k x)

end FD56
