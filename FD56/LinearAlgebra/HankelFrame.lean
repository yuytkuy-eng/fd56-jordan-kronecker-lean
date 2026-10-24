/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.BlockHankelShift

/-! A polynomial frame constructed by inverting the square block Hankel matrix. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [CommRing K] {b c : ℕ}

def hankelFrameTop (i : Fin c) (w : Fin c ⊕ Fin b) : K :=
  match w with
  | Sum.inl k => if i=k then 1 else 0
  | Sum.inr _ => 0

def hankelFrameBoundary (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K) :
    Matrix (Σ j, Fin (h j)) (Fin c ⊕ Fin b) K := fun jr w =>
  match w with
  | Sum.inl i => -a jr.1 i (jr.2.val+g i)
  | Sum.inr j => if jr.1=j ∧ jr.2.val+1=h jr.1 then 1 else 0

def hankelFrameLow (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K) :
    Matrix (Σ i, Fin (g i)) (Fin c ⊕ Fin b) K :=
  B * hankelFrameBoundary h g a

def hankelFrame (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K) :
    Matrix (Fin c) (Fin c ⊕ Fin b) K[X] := fun i w =>
  hankelCoefficientPolynomial g (fun k => hankelFrameLow h g a B k w) i +
    monomial (g i) (hankelFrameTop i w)

theorem hankelFrame_coeff_low (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (i : Fin c) (w : Fin c ⊕ Fin b) (s : Fin (g i)) :
    (hankelFrame h g a B i w).coeff s.val = hankelFrameLow h g a B ⟨i,s⟩ w := by
  simp [hankelFrame,hankelCoefficientPolynomial_coeff,
    coeff_monomial,Nat.ne_of_gt s.isLt]

theorem hankelFrame_coeff_top (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (i : Fin c) (w : Fin c ⊕ Fin b) :
    (hankelFrame h g a B i w).coeff (g i) = hankelFrameTop i w := by
  simp [hankelFrame,hankelCoefficientPolynomial_top_coeff]

theorem hankelFrame_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (i : Fin c) (w : Fin c ⊕ Fin b) :
    (hankelFrame h g a B i w).natDegree ≤ g i := by
  apply (natDegree_add_le _ _).trans
  apply max_le
  · apply natDegree_sum_le_of_forall_le
    intro s _
    exact (natDegree_monomial_le _).trans s.isLt.le
  · exact natDegree_monomial_le _

theorem hankelFrame_leading_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K) :
    Function.Injective (Matrix.mulVec (fun w i => (hankelFrame h g a B i w).coeff (g i))) := by
  intro x y hxy
  funext i
  have hh := congrFun hxy (Sum.inl i)
  simpa [Matrix.mulVec,dotProduct,hankelFrame_coeff_top,hankelFrameTop,eq_comm] using hh

theorem hankelFrame_low_action (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hB : blockHankel h g a * B = 1)
    (jr : Σ j, Fin (h j)) (w : Fin c ⊕ Fin b) :
    (∑ i, ∑ s : Fin (g i), a jr.1 i (jr.2.val+s.val) *
      (hankelFrame h g a B i w).coeff s.val) = hankelFrameBoundary h g a jr w := by
  simp only [hankelFrame_coeff_low]
  have hh := congrFun (congrFun
    (show blockHankel h g a * hankelFrameLow h g a B = hankelFrameBoundary h g a by
      rw [hankelFrameLow,← Matrix.mul_assoc,hB,Matrix.one_mul]) jr) w
  simpa only [Matrix.mul_apply,Fintype.sum_sigma,blockHankel] using hh

theorem hankelFrame_action (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hB : blockHankel h g a * B = 1)
    (jr : Σ j, Fin (h j)) (w : Fin c ⊕ Fin b) :
    polynomialHankelAction (fun i => g i+1) a
      (fun i => hankelFrame h g a B i w) jr.1 jr.2.val =
      match w with
      | Sum.inl _ => 0
      | Sum.inr j => if jr.1=j ∧ jr.2.val+1=h jr.1 then 1 else 0 := by
  unfold polynomialHankelAction
  simp_rw [Fin.sum_univ_castSucc]
  simp only [Fin.coe_castSucc,Fin.val_last,hankelFrame_coeff_top,Finset.sum_add_distrib]
  rw [hankelFrame_low_action h g a B hB jr w]
  cases w with
  | inl k => simp [hankelFrameBoundary,hankelFrameTop]
  | inr j => simp [hankelFrameBoundary,hankelFrameTop]

theorem hankelFrame_action_zero (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hB : blockHankel h g a * B = 1)
    (j : Fin b) (r : ℕ) (hr : r+1 < h j) (w : Fin c ⊕ Fin b) :
    polynomialHankelAction (fun i => g i+1) a
      (fun i => hankelFrame h g a B i w) j r = 0 := by
  have hh := hankelFrame_action h g a B hB ⟨j,⟨r,by omega⟩⟩ w
  cases w <;> simpa [Nat.ne_of_lt hr] using hh

end FD56
