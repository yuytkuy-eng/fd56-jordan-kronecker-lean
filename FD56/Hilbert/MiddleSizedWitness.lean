/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleBetaWitness

/-! Balanced beta witnesses on arbitrary finite index types in the middle
dimension range. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem middle_beta_dimension_identity (m s d : ℕ) (hs : s ≤ m) :
    m * (2 * d + 3) - (m + s) * (d + 3) =
      (m - s) * (d + 1) - (m + 2 * s) := by
  apply tsub_eq_tsub_of_add_eq_add
  have h := congrArg (fun x : ℕ => x * (d + 1)) (Nat.sub_add_cancel hs)
  nlinarith

variable {K m n : Type*} [Field K] [Fintype m] [Fintype n]

theorem exists_middle_sized_beta_witness
    (hmn : Fintype.card m < Fintype.card n)
    (hnm : Fintype.card n < 2 * Fintype.card m) :
    ∃ (M : Matrix n n K[X]) (P : Matrix m n K[X]),
      DegreeBound M 1 ∧ DegreeBound P 1 ∧
      ∀ d, Module.finrank K (boundedBetaKernel M P d) =
        Fintype.card m * (2 * d + 3) - Fintype.card n * (d + 3) := by
  classical
  let s := Fintype.card n - Fintype.card m
  let e := rectangularBlockLengths (Fintype.card m) s
  have hs : 0 < s := by dsimp [s]; omega
  have hslt : s < Fintype.card m := by dsimp [s]; omega
  have hcards : Fintype.card
      (Fin (Fintype.card m % s) ⊕ Fin (s - Fintype.card m % s)) = s := by
    simp only [Fintype.card_sum, Fintype.card_fin]
    have hmod := Nat.mod_lt (Fintype.card m) hs
    omega
  have hsum : ∑ i, e i = Fintype.card m := by
    simpa [e, rectangularBlockLengths, Fintype.sum_sum_type] using
      (rectangular_balanced_rows (Fintype.card m) s hs).symm
  have hsum2 : ∑ i, (e i + 2) = Fintype.card m + 2 * s := by
    rw [Finset.sum_add_distrib, hsum]
    simp [hcards, Nat.mul_comm]
  obtain ⟨M, hM, hH⟩ := exists_affine_middle_balanced_beta_kernel (K := K) e
    (rectangularBlockLengths_adjacent (Fintype.card m) s) (by rw [hcards, hsum]; exact hslt)
  let er := balancedRowEquiv hmn
  let ec := balancedColumnEquiv hmn
  refine ⟨M.submatrix ec ec, (rectangularBlockPencil e).submatrix er ec,
    (fun i j => hM (ec i) (ec j)), (fun i j => rectangularBlockPencil_degree e (er i) (ec j)), ?_⟩
  intro d
  rw [beta_kernel_reindex_finrank, hH, hsum, hcards, hsum2]
  have hn : Fintype.card n = Fintype.card m + s := by dsimp [s]; omega
  rw [hn]
  exact (middle_beta_dimension_identity (Fintype.card m) s d hslt.le).symm

end FD56
