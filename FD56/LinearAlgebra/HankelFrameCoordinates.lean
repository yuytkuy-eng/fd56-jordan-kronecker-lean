/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelFrame

/-! Recovery of the constant parameters of a Hankel frame. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {b c : ℕ}

theorem polynomialHankelAction_mulVec {w : Type*} [Fintype w]
    (g : Fin c → ℕ) (a : Fin b → Fin c → ℕ → R)
    (P : Matrix (Fin c) w R[X]) (x : w → R) (j : Fin b) (r : ℕ) :
    polynomialHankelAction g a (P *ᵥ fun k => C (x k)) j r =
      ∑ k, polynomialHankelAction g a (fun i => P i k) j r * x k := by
  simp only [polynomialHankelAction, Matrix.mulVec, dotProduct,
    finset_sum_coeff, coeff_mul_C, Finset.mul_sum, Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]

theorem hankelFrame_mulVec_top (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (x : Fin c ⊕ Fin b → R) (i : Fin c) :
    ((hankelFrame h g a B *ᵥ fun w => C (x w)) i).coeff (g i) = x (Sum.inl i) := by
  simp [Matrix.mulVec,dotProduct,finset_sum_coeff,coeff_mul_C,
    hankelFrame_coeff_top,hankelFrameTop]

theorem hankelFrame_mulVec_last_action (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a * B = 1)
    (x : Fin c ⊕ Fin b → R) (j : Fin b) (hj : 0 < h j) :
    polynomialHankelAction (fun i => g i+1) a
      (hankelFrame h g a B *ᵥ fun w => C (x w)) j (h j-1) = x (Sum.inr j) := by
  rw [polynomialHankelAction_mulVec]
  have he := hankelFrame_action h g a B hB (⟨j,⟨h j-1,by omega⟩⟩ : Σ j, Fin (h j))
  simp only at he
  simp_rw [he]
  simp [Fintype.sum_sum_type,show h j-1+1=h j by omega]

theorem hankelFrame_constant_parameters_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : blockHankel h g a * B = 1) (hh : ∀ j, 0 < h j) :
    Function.Injective (fun x : Fin c ⊕ Fin b → R =>
      hankelFrame h g a B *ᵥ fun w => C (x w)) := by
  intro x y hxy
  funext w
  cases w with
  | inl i =>
    have he := congrArg (fun p : Fin c → R[X] => (p i).coeff (g i)) hxy
    simpa only [hankelFrame_mulVec_top] using he
  | inr j =>
    have he := congrArg (fun p => polynomialHankelAction (fun i => g i+1) a p j (h j-1)) hxy
    simpa only [hankelFrame_mulVec_last_action h g a B hB _ j (hh j)] using he

def hankelFrameParameters (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R) (p : Fin c → R[X]) : Fin c ⊕ Fin b → R :=
  Sum.elim (fun i => (p i).coeff (g i))
    (fun j => polynomialHankelAction (fun i => g i+1) a p j (h j-1))

theorem hankelFrame_reconstruct (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hB : B * blockHankel h g a = 1)
    (p : Fin c → R[X]) (hp : ∀ i, (p i).natDegree ≤ g i)
    (hz : ∀ j r, r+1 < h j → polynomialHankelAction (fun i => g i+1) a p j r=0) :
    hankelFrame h g a B *ᵥ (fun w => C (hankelFrameParameters h g a p w)) = p := by
  let x := hankelFrameParameters h g a p
  let low : (Σ i, Fin (g i)) → R := fun is => (p is.1).coeff is.2.val
  have hb : hankelFrameBoundary h g a *ᵥ x = blockHankel h g a *ᵥ low := by
    funext jr
    have hf : polynomialHankelAction (fun i => g i+1) a p jr.1 jr.2.val =
        if jr.2.val+1=h jr.1 then x (Sum.inr jr.1) else 0 := by
      split_ifs with he
      · have he' : jr.2.val=h jr.1-1 := by omega
        simp only [he',x,hankelFrameParameters,Sum.elim_inr]
      · exact hz jr.1 jr.2.val (by have := jr.2.isLt; omega)
    simp only [polynomialHankelAction] at hf
    simp_rw [Fin.sum_univ_castSucc] at hf
    simp only [Fin.coe_castSucc,Fin.val_last,Finset.sum_add_distrib] at hf
    simp only [Matrix.mulVec,dotProduct,hankelFrameBoundary,Fintype.sum_sum_type,
      blockHankel,Fintype.sum_sigma,low,neg_mul,Finset.sum_neg_distrib]
    have hs : (∑ j : Fin b, (if jr.1=j ∧ jr.2.val+1=h jr.1 then (1:R) else 0)*x (Sum.inr j)) =
        if jr.2.val+1=h jr.1 then x (Sum.inr jr.1) else 0 := by
      by_cases he : jr.2.val+1=h jr.1 <;> simp [he]
    rw [hs,← hf]
    change -(∑ i, a jr.1 i (jr.2.val+g i)*(p i).coeff (g i)) +
      ((∑ i, ∑ s : Fin (g i), a jr.1 i (jr.2.val+s.val)*(p i).coeff s.val) +
      ∑ i, a jr.1 i (jr.2.val+g i)*(p i).coeff (g i)) = _
    abel
  have hl : hankelFrameLow h g a B *ᵥ x = low := by
    rw [hankelFrameLow,← Matrix.mulVec_mulVec,hb,Matrix.mulVec_mulVec,hB,Matrix.one_mulVec]
  funext i
  ext k
  by_cases hk : k < g i
  · simp only [Matrix.mulVec,dotProduct,finset_sum_coeff,coeff_mul_C]
    simp_rw [hankelFrame_coeff_low h g a B i _ (⟨k,hk⟩ : Fin (g i))]
    exact congrFun hl ⟨i,⟨k,hk⟩⟩
  · by_cases he : k=g i
    · subst k
      exact hankelFrame_mulVec_top h g a B x i
    · have hgt : g i < k := by omega
      rw [coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hp i) hgt)]
      simp only [Matrix.mulVec,dotProduct,finset_sum_coeff,coeff_mul_C]
      apply Finset.sum_eq_zero
      intro w _
      rw [coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hankelFrame_degree h g a B i w) hgt),zero_mul]

end FD56
