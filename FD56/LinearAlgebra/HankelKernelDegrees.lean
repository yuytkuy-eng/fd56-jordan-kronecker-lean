/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.HankelKernelColumns

/-! The explicit kernel columns have the prescribed degrees and independent leading terms. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {R : Type*} [CommRing R] [Nontrivial R] {b c : ℕ}

def hankelKernelBoundaryPart (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (j l : Fin b) : R[X] :=
  ∑ i, ∑ s : Fin (g i), C (a j i (h j+s.val))*hankelInverseColumn h g B ⟨i,s⟩ l

theorem hankelKernelBoundaryPart_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (j l : Fin b) (hl : 0<h l) :
    (hankelKernelBoundaryPart h g a B j l).natDegree < h l := by
  have he : (hankelKernelBoundaryPart h g a B j l).natDegree ≤ h l-1 := by
    apply natDegree_sum_le_of_forall_le
    intro i _
    apply natDegree_sum_le_of_forall_le
    intro s _
    apply (natDegree_C_mul_le _ _).trans
    have := hankelInverseColumn_degree h g B ⟨i,s⟩ l hl
    omega
  omega

theorem hankelKernelMatrix_degree (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (w : Fin c ⊕ Fin b) (l : Fin b) :
    (hankelKernelMatrix h g a B hg w l).natDegree ≤ h l := by
  cases w with
  | inl i => exact (hankelInverseColumn_degree h g B _ l (hh l)).le
  | inr j =>
    change (hankelKernelBoundaryPart h g a B j l - if j=l then X^(h l) else 0).natDegree ≤ _
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact (hankelKernelBoundaryPart_degree h g a B j l (hh l)).le
    · split_ifs <;> simp

theorem hankelKernelMatrix_leading_left (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (i : Fin c) (l : Fin b) :
    (hankelKernelMatrix h g a B hg (Sum.inl i) l).coeff (h l)=0 :=
  coeff_eq_zero_of_natDegree_lt (hankelInverseColumn_degree h g B _ l (hh l))

theorem hankelKernelMatrix_leading_right (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (j l : Fin b) :
    (hankelKernelMatrix h g a B hg (Sum.inr j) l).coeff (h l)=
      if j=l then -1 else 0 := by
  change (hankelKernelBoundaryPart h g a B j l - if j=l then X^(h l) else 0).coeff (h l)=_
  rw [coeff_sub,coeff_eq_zero_of_natDegree_lt (hankelKernelBoundaryPart_degree h g a B j l (hh l))]
  split_ifs <;> simp

theorem hankelKernelMatrix_leading_injective (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → R)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) R)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) :
    Function.Injective (Matrix.mulVec (fun w l => (hankelKernelMatrix h g a B hg w l).coeff (h l))) := by
  intro x y hxy
  funext j
  have he := congrFun hxy (Sum.inr j)
  simpa [Matrix.mulVec,dotProduct,hankelKernelMatrix_leading_right h g a B hh hg] using he

end FD56
