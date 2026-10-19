/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BlockSum
import FD56.Hilbert.HilbertRecovery

/-! Hilbert functions and uniqueness of the indices of canonical block sums. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

def KroneckerSumIndex : List ℕ → Type
  | [] => Fin 0
  | m :: ms => (Fin m ⊕ Fin (m + 1)) ⊕ KroneckerSumIndex ms

instance kroneckerSumIndexFintype (ms : List ℕ) : Fintype (KroneckerSumIndex ms) := by
  induction ms with
  | nil => exact inferInstanceAs (Fintype (Fin 0))
  | cons m ms ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((Fin m ⊕ Fin (m + 1)) ⊕ KroneckerSumIndex ms))

def kroneckerSumPencil : (ms : List ℕ) →
    Matrix (KroneckerSumIndex ms) (KroneckerSumIndex ms) K[X]
  | [] => 0
  | m :: ms => Matrix.fromBlocks (kroneckerBlockPencil m) 0 0 (kroneckerSumPencil ms)

theorem kroneckerSum_kernel_hilbert (ms : List ℕ) (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (kroneckerSumPencil (K := K) ms) d) =
      (ms.map (fun m => d + 1 - m)).sum := by
  induction ms with
  | nil =>
    haveI : Subsingleton (KroneckerSumIndex [] → BoundedPoly K d) :=
      inferInstanceAs (Subsingleton (Fin 0 → BoundedPoly K d))
    have hz : polynomialKernelAtDegree (kroneckerSumPencil (K := K) []) d = ⊥ := by
      apply (Submodule.eq_bot_iff _).mpr
      intro x _
      exact Subsingleton.elim _ _
    rw [hz]
    exact finrank_bot K (KroneckerSumIndex [] → BoundedPoly K d)
  | cons m ms ih =>
    change Module.finrank K (polynomialKernelAtDegree
      (Matrix.fromBlocks (kroneckerBlockPencil m) 0 0 (kroneckerSumPencil ms)) d) = _
    rw [blockSum_kernel_hilbert, kroneckerBlock_kernel_hilbert, ih]
    rfl

theorem kroneckerSum_kernel_listHilbert (ms : List ℕ) (d : ℕ) :
    (Module.finrank K (polynomialKernelAtDegree
      (kroneckerSumPencil (K := K) ms) d) : ℤ) = listHilbert ms d := by
  rw [kroneckerSum_kernel_hilbert]
  induction ms with
  | nil => simp [listHilbert]
  | cons m ms ih =>
    simp only [List.map_cons, List.sum_cons, Nat.cast_add, listHilbert] at ih ⊢
    rw [ih]
    congr 1
    omega

theorem kroneckerSum_indices_unique (ms ns : List ℕ)
    (h : ∀ d, Module.finrank K (polynomialKernelAtDegree
      (kroneckerSumPencil (K := K) ms) d) =
      Module.finrank K (polynomialKernelAtDegree (kroneckerSumPencil (K := K) ns) d)) :
    ms.Perm ns := by
  apply listHilbert_determines_indices
  intro d
  rw [← kroneckerSum_kernel_listHilbert (K := K) ms d,
    ← kroneckerSum_kernel_listHilbert (K := K) ns d, h d]

end FD56
