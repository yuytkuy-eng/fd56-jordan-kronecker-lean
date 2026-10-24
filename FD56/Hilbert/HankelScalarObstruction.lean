/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.HankelBoundedImage

/-! Scalar lifts are characterized by stacked Hankel coefficient equations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K : Type*} [Field K] {b c : ℕ}

theorem fullHankelAction_single (a : Fin b → Fin c → ℕ → K)
    (p : K[X]) (i : Fin c) (j : Fin b) (r : ℕ) :
    fullHankelAction a (Pi.single i p) j r = hankelFunctional (a j i) r p := by
  simp [fullHankelAction,Pi.single_apply,apply_ite]

theorem hankelFrame_scalar_column_lift_iff (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j)
    (d : ℕ) (i : Fin c) (hd : g i≤d+1) (p : K[X]) (hp : p.natDegree≤d+1) :
    (∃ x : Fin c ⊕ Fin b → K[X], (∀ w, (x w).natDegree≤d+1-g i) ∧
      hankelFrame h g a B *ᵥ x=Pi.single i p) ↔
    ∀ j r, r<h j+g i-(d+2) →
      (∑ s : Fin (d+2), a j i (r+s.val)*p.coeff s.val)=0 := by
  have hb (k : Fin c) : ((Pi.single i p : Fin c → K[X]) k).natDegree≤g k+(d+1-g i) := by
    by_cases hk : k=i
    · subst k
      simpa only [Pi.single_eq_same,Nat.add_sub_of_le hd] using hp
    · simp [Pi.single_eq_of_ne hk]
  rw [hankelFrame_bounded_lift_iff h g a B hBH hHB hh hg hsum (d+1-g i) _ hb]
  simp only [fullHankelAction_single]
  have he (j : Fin b) (r : ℕ) : hankelFunctional (a j i) r p=
      ∑ s : Fin (d+2), a j i (r+s.val)*p.coeff s.val :=
    hankelFunctional_truncated _ r (d+2) p (by omega)
  simp_rw [he]
  constructor <;> intro hz j r hr <;> exact hz j r (by omega)

theorem hankelFrame_scalar_lift_iff (h : Fin b → ℕ) (g : Fin c → ℕ)
    (a : Fin b → Fin c → ℕ → K)
    (B : Matrix (Σ i, Fin (g i)) (Σ j, Fin (h j)) K)
    (hBH : B*blockHankel h g a=1) (hHB : blockHankel h g a*B=1)
    (hh : ∀ j, 0<h j) (hg : ∀ i, 0<g i) (hsum : ∑ i, g i=∑ j, h j)
    (d : ℕ) (hd : ∀ i, g i≤d+1) (p : K[X]) (hp : p.natDegree≤d+1) :
    (∀ i, ∃ x : Fin c ⊕ Fin b → K[X], (∀ w, (x w).natDegree≤d+1-g i) ∧
      hankelFrame h g a B *ᵥ x=Pi.single i p) ↔
    ∀ i j r, r<h j+g i-(d+2) →
      (∑ s : Fin (d+2), a j i (r+s.val)*p.coeff s.val)=0 := by
  exact forall_congr' fun i =>
    hankelFrame_scalar_column_lift_iff h g a B hBH hHB hh hg hsum d i (hd i) p hp

end FD56
