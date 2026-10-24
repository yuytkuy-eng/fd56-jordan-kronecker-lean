/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformCubicCompletion
import FD56.Hilbert.CubicTwoIteration

/-! Iterated uniform completions, including arbitrary extension widths. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def uniformCubicAlpha {r : ℕ} (w : ℕ) (alpha : Fin r → ℕ) :
    (k : ℕ) → IteratedFin w r k → ℕ
  | 0 => alpha
  | k+1 => Sum.elim (fun _ => 1) (uniformCubicAlpha w alpha k)

theorem uniformCubicAlpha_range {r : ℕ} (w : ℕ) (alpha : Fin r → ℕ)
    (ha : ∀ j, 0<alpha j ∧ alpha j≤2) (k : ℕ) (j : IteratedFin w r k) :
    0<uniformCubicAlpha w alpha k j ∧ uniformCubicAlpha w alpha k j≤2 := by
  induction k with
  | zero => exact ha j
  | succ k ih =>
    cases j with
    | inl j => simp [uniformCubicAlpha]
    | inr j => exact ih j

theorem uniformCubicAlpha_fiber {r : ℕ} (w : ℕ) (alpha : Fin r → ℕ) (k d : ℕ) :
    Fintype.card {i // uniformCubicAlpha w alpha k i=d}=
      (if 1=d then w*k else 0)+Fintype.card {i // alpha i=d} := by
  induction k with
  | zero => simp [uniformCubicAlpha]; rfl
  | succ k ih =>
    rw [Fintype.card_subtype,Finset.card_filter]
    change (∑ i : Fin w ⊕ IteratedFin w r k,
      if Sum.elim (fun _ => 1) (uniformCubicAlpha w alpha k) i=d then 1 else 0)=_
    rw [Fintype.sum_sum_type]
    simp only [Sum.elim_inl,Sum.elim_inr,Finset.sum_const,Finset.card_univ,
      Fintype.card_fin,smul_eq_mul]
    have hsum : (∑ i : IteratedFin w r k,
        if uniformCubicAlpha w alpha k i=d then 1 else 0)=
        Fintype.card {i // uniformCubicAlpha w alpha k i=d} := by
      rw [Fintype.card_subtype,Finset.card_filter]
    rw [hsum,ih]
    by_cases hd : 1=d
    · subst d
      simp only [ite_true,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        smul_eq_mul,mul_one,Nat.mul_succ]
      omega
    · simp only [if_neg hd,Finset.sum_const_zero,zero_add]

variable {K : Type*} [Field K]

def uniformCubicIteration {w m r b : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin w) (Fin w) K[X]}
    (C : UniformCubicCompletion (m := Fin m) alpha b W) :
    (k : ℕ) → UniformCubicCompletion (m := IteratedFin w m k)
      (uniformCubicAlpha w alpha k) (cubicIterationBound b k) W
  | 0 => C
  | k+1 => (uniformCubicIteration C k).extend

theorem uniformCubicIteration_zero {w m r b : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin w) (Fin w) K[X]}
    (C : UniformCubicCompletion (m := Fin m) alpha b W)
    (hb : 3≤b) (ha : ∀ j, 0<alpha j ∧ alpha j≤2)
    (hjet : Function.Injective (Matrix.mulVec
      (fun (ij : Fin w × Fin w) (k : Fin 3) => (W ij.1 ij.2).coeff (2-k.val))))
    (hzero : C.ScalarZero b) (k : ℕ) :
    (uniformCubicIteration C k).ScalarZero (cubicIterationBound b k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    apply UniformCubicCompletion.scalar_zero_extend _ _ hjet ih
    intro i
    have hh := (uniformCubicAlpha_range w alpha ha k i).2
    rw [cubicIterationBound_eq]
    omega

theorem uniformCubicIteration_selector {w m r b t : ℕ} {alpha : Fin r → ℕ}
    {W : Matrix (Fin w) (Fin w) K[X]}
    (C : UniformCubicCompletion (m := Fin m) alpha b W)
    (hb : 2≤b) (ha : ∀ j, 0<alpha j ∧ alpha j≤2) (f : Fin t → ℕ)
    (hzero : C.ScalarSelector (b+1) f) (k : ℕ) :
    (uniformCubicIteration C k).ScalarSelector (cubicIterationBound b k+1)
      (cubicIterationSelector (fun j : Fin 3 => j.val) f k) := by
  induction k with
  | zero => exact hzero
  | succ k ih =>
    change (uniformCubicIteration C k).extend.ScalarSelector
      (cubicIterationBound b k+3+1) _
    rw [show cubicIterationBound b k+3+1=(cubicIterationBound b k+1)+3 by omega]
    apply UniformCubicCompletion.scalar_selector_extend _ _ _ _ ih
    intro i
    have hh := (uniformCubicAlpha_range w alpha ha k i).2
    rw [cubicIterationBound_eq]
    omega

end FD56
