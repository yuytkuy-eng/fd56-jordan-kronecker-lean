/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.DualConstant
import FD56.LinearAlgebra.PluckerDifferential
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Nine leading coefficient constraints for an equal-degree three-column
frame, retaining one common nonzero scalar on every maximal minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

theorem three_column_equal_normalization {K n : Type*} [Field K]
    (G : Matrix n (Fin 3) K[X]) (h : ℕ) (pivot : Fin 3 → n)
    (hG : ∀ i j, (G i j).natDegree≤h)
    (hpivot : (Matrix.of fun i j => (G (pivot i) j).coeff h).det≠0) :
    ∃ (H : Matrix n (Fin 3) K[X]) (c : K), c≠0 ∧
      (∀ i j, (H i j).natDegree≤h) ∧
      (∀ i j, (H (pivot i) j).coeff h=(1 : Matrix (Fin 3) (Fin 3) K) i j) ∧
      ∀ row : Fin 3 → n, pluckerMinorVector G row=C c*pluckerMinorVector H row := by
  let Q : Matrix (Fin 3) (Fin 3) K := fun i j => (G (pivot i) j).coeff h
  have hQ : IsUnit Q.det := isUnit_iff_ne_zero.mpr hpivot
  let H := G*(Q⁻¹).map C
  have hGH : H*Q.map C=G := by
    dsimp only [H]
    rw [Matrix.mul_assoc,← Matrix.map_mul,Matrix.nonsing_inv_mul Q hQ]
    simp
  refine ⟨H,Q.det,hpivot,mul_constant_row_degree G Q⁻¹ (fun _ => h) hG,?_,?_⟩
  · intro i j
    have he := congrFun (congrFun (mul_constant_row_leading G Q⁻¹ (fun _ => h)) (pivot i)) j
    change (H (pivot i) j).coeff h=(Q*Q⁻¹) i j at he
    rw [he,Matrix.mul_nonsing_inv Q hQ]
  · intro row
    conv_lhs => rw [← hGH]
    unfold pluckerMinorVector
    rw [Matrix.submatrix_mul H (Q.map C) row id id Function.bijective_id,
      Matrix.submatrix_id_id,Matrix.det_mul]
    have hdet : (Q.map C).det=C Q.det := by
      simpa only [RingHom.mapMatrix_apply] using (Polynomial.C.map_det Q).symm
    rw [hdet]
    exact mul_comm _ _

end FD56
