/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.AlternatingCrossDeterminant

/-! A constant invertible change between finite coordinate sets scales a pencil determinant by a square. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem constant_rectangular_congruence_det {K a b : Type*} [Field K]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (e : b ≃ a) (S : Matrix a b K) (T : Matrix b a K) (hST : S*T=1)
    (P : Matrix a a K[X]) :
    ∃ c : K, c ≠ 0 ∧
      ((S.map C).transpose*P*S.map C).det=C c^2*P.det := by
  let U := S.submatrix e (Equiv.refl b)
  let V := T.submatrix (Equiv.refl b) e
  have hUV : U*V=1 := by
    dsimp only [U,V]
    rw [Matrix.submatrix_mul_equiv,hST,Matrix.submatrix_one_equiv]
  have hc : U.det≠0 := by
    have h := congrArg Matrix.det hUV
    rw [Matrix.det_mul,Matrix.det_one] at h
    exact left_ne_zero_of_mul (by rw [h]; exact one_ne_zero)
  refine ⟨U.det,hc,?_⟩
  have hcong : (S.map C).transpose*P*S.map C =
      (U.map C).transpose*(P.submatrix e e)*U.map C := by
    dsimp only [U]
    simp only [← Matrix.submatrix_map,Matrix.transpose_submatrix]
    rw [Matrix.submatrix_mul_equiv,Matrix.submatrix_mul_equiv]
    rfl
  rw [hcong,Matrix.det_mul,Matrix.det_mul,Matrix.det_transpose,
    Matrix.det_submatrix_equiv_self]
  change ((C.mapMatrix U).det * P.det * (C.mapMatrix U).det)=_
  rw [← RingHom.map_det]
  ring

end FD56
