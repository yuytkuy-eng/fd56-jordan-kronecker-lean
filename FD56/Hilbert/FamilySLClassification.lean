/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FamilySLRealization
import FD56.Hilbert.FamilySLClosure
import FD56.Hilbert.GenericKernelBound

/-! The actual generic SL minimal degrees for (n,m)=(11k,8k), with all
auxiliary realization and generic rank conditions discharged. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_family_slHilbert_five {K : Type*} [Field K]
    (k : ℕ) (hk : 0 < k) :
    slHilbert (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) 5 = k ^ 2 := by
  let i₀ : Fin (11 * k) := ⟨0, by omega⟩
  obtain ⟨M, P, hM, hP, hH⟩ := exists_family_sl_degree_five_witness (K := K) k hk
  apply Nat.le_antisymm
  · exact (generic_slHilbert_le_witness M P hM hP i₀ 5).trans_eq hH
  · have hb := (generic_middle_slHilbert_bounds (K := K) (m := Fin (8 * k)) i₀
      (by simp; omega) (by simp; omega) 5).1
    have hg := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_family_gl_minimal_degrees (K := K) k hk) 5
    simp only [List.map_append, List.map_replicate, List.sum_append,
      List.sum_replicate, smul_eq_mul] at hg
    norm_num at hg
    simpa only [hg] using hb

theorem generic_family_sl_minimal_degrees {K : Type*} [Field K]
    (k : ℕ) (hk : 0 < k) (i₀ : Fin (11 * k)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) i₀)
      (List.replicate (k ^ 2) 5 ++ List.replicate (6 * k ^ 2 + 8) 6 ++
        List.replicate (8 * k ^ 2 - 7) 7) :=
  generic_family_sl_minimal_degrees_of_degree_five k hk i₀
    (generic_family_slHilbert_five k hk)

theorem generic_family_slHilbert {K : Type*} [Field K]
    (k : ℕ) (hk : 0 < k) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) d =
      k ^ 2 * (d - 4) + (6 * k ^ 2 + 8) * (d - 5) +
        (8 * k ^ 2 - 7) * (d - 6) := by
  let i₀ : Fin (11 * k) := ⟨0, by omega⟩
  rw [slHilbert_eq_matrix_kernel _ _ i₀,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_family_sl_minimal_degrees (K := K) k hk i₀) d]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    smul_eq_mul]
  congr 2

end FD56
