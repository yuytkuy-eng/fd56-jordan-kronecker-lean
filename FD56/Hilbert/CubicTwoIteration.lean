/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.CubicTwoParity

/-! Iteration of the split cubic extension with exact finite cardinalities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def IteratedFin (width base : ℕ) : ℕ → Type
  | 0 => Fin base
  | k+1 => Fin width ⊕ IteratedFin width base k

instance iteratedFinFintype (width base k : ℕ) : Fintype (IteratedFin width base k) := by
  induction k with
  | zero => exact inferInstanceAs (Fintype (Fin base))
  | succ k ih =>
    letI := ih
    exact inferInstanceAs (Fintype (Fin width ⊕ IteratedFin width base k))

instance iteratedFinDecidableEq (width base : ℕ) :
    (k : ℕ) → DecidableEq (IteratedFin width base k)
  | 0 => inferInstanceAs (DecidableEq (Fin base))
  | k+1 => by
    letI := iteratedFinDecidableEq width base k
    exact inferInstanceAs (DecidableEq (Fin width ⊕ IteratedFin width base k))

theorem iteratedFin_card (width base k : ℕ) :
    Fintype.card (IteratedFin width base k)=width*k+base := by
  induction k with
  | zero => simp [IteratedFin]
  | succ k ih =>
    change Fintype.card (Fin width ⊕ IteratedFin width base k)=_
    simp [Fintype.card_sum,ih,Nat.mul_succ]
    omega

def cubicIterationBound (b : ℕ) : ℕ → ℕ
  | 0 => b
  | k+1 => cubicIterationBound b k+3

theorem cubicIterationBound_eq (b k : ℕ) : cubicIterationBound b k=b+3*k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [cubicIterationBound, ih, Nat.mul_succ, Nat.add_assoc]

def cubicIterationAlpha {r : ℕ} (alpha : Fin r → ℕ) :
    (k : ℕ) → IteratedFin 2 r k → ℕ
  | 0 => alpha
  | k+1 => Sum.elim (fun _ => 1) (cubicIterationAlpha alpha k)

theorem cubicIterationAlpha_le {r : ℕ} (alpha : Fin r → ℕ)
    (ha : ∀ j, alpha j≤2) (k : ℕ) (j : IteratedFin 2 r k) :
    cubicIterationAlpha alpha k j≤2 := by
  induction k with
  | zero => exact ha j
  | succ k ih =>
    cases j with
    | inl j => simp [cubicIterationAlpha]
    | inr j => exact ih j

theorem cubicIterationAlpha_positive {r : ℕ} (alpha : Fin r → ℕ)
    (ha : ∀ j, 0<alpha j) (k : ℕ) (j : IteratedFin 2 r k) :
    0<cubicIterationAlpha alpha k j := by
  induction k with
  | zero => exact ha j
  | succ k ih =>
    cases j with
    | inl j => simp [cubicIterationAlpha]
    | inr j => exact ih j

theorem cubicIterationAlpha_fiber {r : ℕ} (alpha : Fin r → ℕ) (k d : ℕ) :
    Fintype.card {i // cubicIterationAlpha alpha k i=d}=
      (if 1=d then 2*k else 0)+Fintype.card {i // alpha i=d} := by
  induction k with
  | zero => simp [cubicIterationAlpha]; rfl
  | succ k ih =>
    rw [Fintype.card_subtype,Finset.card_filter]
    change (∑ i : Fin 2 ⊕ IteratedFin 2 r k,
      if Sum.elim (fun _ => 1) (cubicIterationAlpha alpha k) i=d then 1 else 0)=_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    have hsum : (∑ i : IteratedFin 2 r k,
        if cubicIterationAlpha alpha k i=d then 1 else 0)=
        Fintype.card {i // cubicIterationAlpha alpha k i=d} := by
      rw [Fintype.card_subtype,Finset.card_filter]
    rw [hsum,ih]
    split_ifs <;> simp_all <;> omega

def cubicIterationSelector {w t : ℕ} (step : Fin w → ℕ) (f : Fin t → ℕ) :
    (k : ℕ) → IteratedFin w t k → ℕ
  | 0 => f
  | k+1 => Sum.elim step (fun j => cubicIterationSelector step f k j+3)

variable {K : Type*} [Field K] [CharZero K]

def cubicCompletionIteration {m r b eps : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin 2) (Fin 2) K[X]}
    (C : CubicTwoCompletion (m := Fin m) alpha b eps W) :
    (k : ℕ) → CubicTwoCompletion (m := IteratedFin 2 m k)
      (cubicIterationAlpha alpha k) (cubicIterationBound b k) eps W
  | 0 => C
  | k+1 => (cubicCompletionIteration C k).extend

theorem cubicCompletionIteration_even_zero {m r b : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin 2) (Fin 2) K[X]}
    (C : CubicTwoCompletion (m := Fin m) alpha b 0 W)
    (hW : (4 : K[X]) • W=mixedOneTwoEvenAdjugate)
    (hb : 3≤b) (ha : ∀ j, alpha j≤2) (hzero : C.ScalarZero b) (k : ℕ) :
    (cubicCompletionIteration C k).ScalarZero (cubicIterationBound b k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    apply CubicTwoCompletion.even_zero_extend _ hW _ ih
    intro i
    have hh := cubicIterationAlpha_le alpha ha k i
    rw [cubicIterationBound_eq]
    omega

theorem cubicCompletionIteration_odd_zero {m r b : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin 2) (Fin 2) K[X]}
    (C : CubicTwoCompletion (m := Fin m) alpha b 1 W)
    (hW : (8 : K[X]) • W=mixedOneTwoOddAdjugate)
    (hb : 3≤b) (ha : ∀ j, alpha j≤2) (hzero : C.ScalarZero b) (k : ℕ) :
    (cubicCompletionIteration C k).ScalarZero (cubicIterationBound b k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    apply CubicTwoCompletion.odd_zero_extend _ hW _ ih
    intro i
    have hh := cubicIterationAlpha_le alpha ha k i
    rw [cubicIterationBound_eq]
    omega

theorem cubicCompletionIteration_even_selector {m r b t : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin 2) (Fin 2) K[X]}
    (C : CubicTwoCompletion (m := Fin m) alpha b 0 W)
    (hb : 2≤b) (ha : ∀ j, alpha j≤2) (f : Fin t → ℕ)
    (hzero : C.ScalarSelector (b+1) f) (k : ℕ) :
    (cubicCompletionIteration C k).ScalarSelector (cubicIterationBound b k+1)
      (cubicIterationSelector (fun j : Fin 3 => j.val) f k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    change (cubicCompletionIteration C k).extend.ScalarSelector
      (cubicIterationBound b k+3+1) _
    rw [show cubicIterationBound b k+3+1=cubicIterationBound b k+4 by omega]
    apply CubicTwoCompletion.even_selector_extend _ _ _ ih
    intro i
    have hh := cubicIterationAlpha_le alpha ha k i
    rw [cubicIterationBound_eq]
    omega

theorem cubicCompletionIteration_odd_selector {m r b t : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin 2) (Fin 2) K[X]}
    (C : CubicTwoCompletion (m := Fin m) alpha b 1 W)
    (hW : (8 : K[X]) • W=mixedOneTwoOddAdjugate)
    (hb : 2≤b) (ha : ∀ j, alpha j≤2) (f : Fin t → ℕ)
    (hzero : C.ScalarSelector (b+1) f) (k : ℕ) :
    (cubicCompletionIteration C k).ScalarSelector (cubicIterationBound b k+1)
      (cubicIterationSelector (fun _ : Fin 1 => 0) f k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    change (cubicCompletionIteration C k).extend.ScalarSelector
      (cubicIterationBound b k+3+1) _
    rw [show cubicIterationBound b k+3+1=cubicIterationBound b k+4 by omega]
    apply CubicTwoCompletion.odd_selector_extend _ hW _ _ ih
    intro i
    have hh := cubicIterationAlpha_le alpha ha k i
    rw [cubicIterationBound_eq]
    omega

end FD56
