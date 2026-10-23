/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.UniformGeneralSLClosure
import FD56.Hilbert.UniformGeneralSLRealization
import FD56.Hilbert.UniformGeneralWitness
import FD56.Hilbert.GenericKernelBound
import FD56.Hilbert.UniformPartialSLRealization
import FD56.Hilbert.UniformPartialWitness

/-! Generic SL minimal degrees for every uniform middle family with a ≥ 4. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem generic_uniform_slHilbert_critical_zero {K : Type*} [Field K]
    (a r : ℕ) (ha : 0 < a) (hr : 0 < r) (hcap : a ≤ 3 * (r ^ 2 - 1)) :
    slHilbert (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) (a + 1) = 0 := by
  obtain ⟨G, hG, hGi, hz⟩ := exists_uniform_general_sl_witness (K := K) a r ha hr hcap
  obtain ⟨M, P, hM, hP, hH⟩ :=
    exists_uniform_sl_critical_witness_of_matrix a r ha hr G hG hGi hz
  let i₀ : Fin ((a + 1) * r) := ⟨0, Nat.mul_pos (by omega) hr⟩
  have hb := generic_slHilbert_le_witness M P hM hP i₀ (a + 1)
  exact Nat.eq_zero_of_le_zero (hb.trans_eq hH)

theorem generic_uniform_sl_minimal_degrees_zero_critical {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) (hcap : a ≤ 3 * (r ^ 2 - 1))
    (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (List.replicate ((a - 4) * r ^ 2 + a + 4) (a + 2) ++
        List.replicate (3 * r ^ 2 - (a + 3)) (a + 3)) := by
  have hr2 : 1 ≤ r ^ 2 := by nlinarith
  have ht : a + 3 - 3 * r ^ 2 = 0 := by
    have hh := Nat.sub_add_cancel hr2
    omega
  have hc : slHilbert (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) (a + 1) =
      a + 3 - 3 * r ^ 2 := by
    rw [ht]
    exact generic_uniform_slHilbert_critical_zero a r (by omega) hr hcap
  simpa only [ht, mul_zero, Nat.sub_zero, List.replicate_zero, List.nil_append] using
    generic_uniform_sl_minimal_degrees_of_critical a r ha hr i₀ hc

theorem generic_uniform_slHilbert_critical {K : Type*} [Field K]
    (a r : ℕ) (ha : 1 ≤ a) (hr : 0 < r) :
    slHilbert (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) (a + 1) =
      a + 3 - 3 * r ^ 2 := by
  let i₀ : Fin ((a + 1) * r) := ⟨0, Nat.mul_pos (by omega) hr⟩
  apply le_antisymm
  · obtain ⟨G, hG, hGi, hz⟩ := exists_uniform_partial_sl_witness (K := K) a r (by omega) hr
    obtain ⟨M, P, hM, hP, hH⟩ := exists_uniform_sl_critical_upper_witness_of_matrix
      a r (by omega) hr G hG hGi (a - 3 * (r ^ 2 - 1))
      (fun j => 3 * (r ^ 2 - 1) + j.val) hz
    have hb := (generic_slHilbert_le_witness M P hM hP i₀ (a + 1)).trans hH
    have hr2 : 1 ≤ r ^ 2 := by nlinarith
    have hh := Nat.sub_add_cancel hr2
    have he : a - 3 * (r ^ 2 - 1) = a + 3 - 3 * r ^ 2 := by omega
    rwa [he] at hb
  · exact generic_uniform_slHilbert_critical_lower a r ha hr (by simp) (by simp) i₀

theorem generic_uniform_sl_minimal_degrees {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) (i₀ : Fin ((a + 1) * r)) :
    HasMinimalKernelDegrees (slEquationMatrix
      (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) i₀)
      (List.replicate (a + 3 - 3 * r ^ 2) (a + 1) ++
        List.replicate ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) (a + 2) ++
        List.replicate (3 * r ^ 2 - (a + 3)) (a + 3)) :=
  generic_uniform_sl_minimal_degrees_of_critical a r ha hr i₀
    (generic_uniform_slHilbert_critical a r (by omega) hr)

theorem generic_uniform_slHilbert {K : Type*} [Field K]
    (a r : ℕ) (ha : 4 ≤ a) (hr : 0 < r) (d : ℕ) :
    slHilbert (genericAffineSquare K (Fin ((a + 1) * r)) (Fin (a * r)))
      (genericAffineRows K (Fin ((a + 1) * r)) (Fin (a * r))) d =
      (a + 3 - 3 * r ^ 2) * (d + 1 - (a + 1)) +
      ((a - 4) * r ^ 2 + a + 4 - 2 * (a + 3 - 3 * r ^ 2)) * (d + 1 - (a + 2)) +
      (3 * r ^ 2 - (a + 3)) * (d + 1 - (a + 3)) := by
  let i₀ : Fin ((a + 1) * r) := ⟨0, Nat.mul_pos (by omega) hr⟩
  rw [slHilbert_eq_matrix_kernel _ _ i₀,
    (hasMinimalKernelDegrees_iff_hilbert _ _).mp
      (generic_uniform_sl_minimal_degrees (K := K) a r ha hr i₀) d]
  simp only [List.map_append, List.map_replicate, List.sum_append,
    List.sum_replicate, smul_eq_mul]

end FD56
