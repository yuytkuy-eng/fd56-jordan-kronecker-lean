/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericMiddleSLHigh
import FD56.Hilbert.FamilyGL

/-! Proved SL Hilbert values for the family (n,m)=(11k,8k). -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_family_slHilbert_high {K : Type*} [Field K]
    (k : ℕ) (hk : 0 < k) (d : ℕ) (hd : 6 ≤ d) :
    slHilbert (genericAffineSquare K (Fin (11 * k)) (Fin (8 * k)))
      (genericAffineRows K (Fin (11 * k)) (Fin (8 * k))) d =
      k ^ 2 * (d - 4) + 6 * k ^ 2 * (d - 5) +
        8 * k ^ 2 * (d - 6) + (d + 2) := by
  have hn : 11 * k - 8 * k = 3 * k := by omega
  have hs : 8 * k - 3 * k = 5 * k := by omega
  have hD : 8 * k + 2 * (3 * k) = 14 * k := by ring
  have hda : 8 * k / (3 * k) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  have hdb : 14 * k / (5 * k) = 2 := Nat.div_eq_of_lt_le (by omega) (by omega)
  rw [generic_middle_slHilbert_high (⟨0, by omega⟩ : Fin (11 * k))
    (by simp; omega) (by simp; omega) d (by
      simpa only [Fintype.card_fin, hn, hs, hD, hda, hdb] using hd)]
  rw [(hasMinimalKernelDegrees_iff_hilbert _ _).mp (generic_family_gl_minimal_degrees k hk) d]
  simp only [List.map_append, List.map_replicate, List.sum_append, List.sum_replicate,
    smul_eq_mul]
  congr 3

end FD56
