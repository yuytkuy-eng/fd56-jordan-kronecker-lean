/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.FieldSLMatrix

/-! The scalar correction realizes the one-dimensional field extension from
GL to SL when the GL radical is traceless. No polynomial splitting is asserted. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m] [Nonempty n]

theorem fieldSL_residual_scalar (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (z : MatrixAlgebraSpace K n m) (hz : z ∈ fieldSLRadical M P) :
    stabilizerResidual M P z = (stabilizerResidual M P z) i₀ i₀ • (1 : Matrix n n K) := by
  obtain ⟨_, _, c, hc⟩ := (fieldSLRadical_iff_equations M P z).mp hz
  have h : stabilizerResidual M P z = c • (1 : Matrix n n K) := by
    change M * z.1 - z.1 * M - z.2 * P = _
    rw [hc, add_sub_cancel_left]
  rw [h]
  simp

theorem fieldSL_scalar_zero_iff (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (z : MatrixAlgebraSpace K n m) (hz : z ∈ fieldSLRadical M P) :
    (stabilizerResidual M P z) i₀ i₀ = 0 ↔ z ∈ glStabilizerSpace M P := by
  constructor
  · intro h
    have he := fieldSL_residual_scalar M P i₀ z hz
    rw [h, zero_smul] at he
    exact ⟨((fieldSLRadical_iff_equations M P z).mp hz).2.1, sub_eq_zero.mp he⟩
  · rintro ⟨_, h⟩
    simp [stabilizerResidual, h]

theorem exists_fieldSL_scalar_one_of_finrank (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (hdim : Module.finrank K (glStabilizerSpace M P) <
      Module.finrank K (fieldSLRadical M P)) :
    ∃ z ∈ fieldSLRadical M P, stabilizerResidual M P z = (1 : Matrix n n K) := by
  have hex : ∃ z ∈ fieldSLRadical M P, (stabilizerResidual M P z) i₀ i₀ ≠ 0 := by
    by_contra h
    push_neg at h
    have hle : fieldSLRadical M P ≤ glStabilizerSpace M P := by
      intro z hz
      exact (fieldSL_scalar_zero_iff M P i₀ z hz).mp (h z hz)
    have hd := Submodule.finrank_mono hle
    exact (Nat.not_le_of_lt hdim) hd
  obtain ⟨z, hz, hc⟩ := hex
  refine ⟨((stabilizerResidual M P z) i₀ i₀)⁻¹ • z,
    (fieldSLRadical M P).smul_mem _ hz, ?_⟩
  rw [map_smul, fieldSL_residual_scalar M P i₀ z hz]
  simp [smul_smul, hc]

theorem exists_fieldSL_scalar_one (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (htrace : ∀ z : glStabilizerSpace M P, Matrix.trace z.val.1 = 0) :
    ∃ z ∈ fieldSLRadical M P, stabilizerResidual M P z = (1 : Matrix n n K) := by
  apply exists_fieldSL_scalar_one_of_finrank M P i₀
  rw [fieldSLRadical_finrank M P htrace]
  exact Nat.lt_succ_self _

theorem fieldSL_scalar_decomposition (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (z₀ : MatrixAlgebraSpace K n m) (hz₀ : z₀ ∈ fieldSLRadical M P)
    (hunit : stabilizerResidual M P z₀ = (1 : Matrix n n K))
    (z : MatrixAlgebraSpace K n m) (hz : z ∈ fieldSLRadical M P) :
    ∃! c : K, z - c • z₀ ∈ glStabilizerSpace M P := by
  let c := (stabilizerResidual M P z) i₀ i₀
  have hs (a : K) : z - a • z₀ ∈ fieldSLRadical M P :=
    (fieldSLRadical M P).sub_mem hz ((fieldSLRadical M P).smul_mem a hz₀)
  have he (a : K) : (stabilizerResidual M P (z - a • z₀)) i₀ i₀ = c - a := by
    rw [map_sub, map_smul, hunit]
    simp [c]
  refine ⟨c, (fieldSL_scalar_zero_iff M P i₀ _ (hs c)).mp ?_, ?_⟩
  · rw [he, sub_self]
  · intro a ha
    have h := (fieldSL_scalar_zero_iff M P i₀ _ (hs a)).mpr ha
    rw [he] at h
    exact (sub_eq_zero.mp h).symm

end FD56
