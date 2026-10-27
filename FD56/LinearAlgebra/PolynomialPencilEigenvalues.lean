/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialPencilPrimaryData
import Mathlib.LinearAlgebra.Eigenspace.Minpoly

/-! Eigenvalues of the relative operator are finite roots of the actual pencil determinant. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem polynomialPencilOperator_charpoly (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hd : Matrix.det (fun r s => (H r s).coeff 1)≠0) :
    let B : Matrix n n K := fun r s => (H r s).coeff 1
    (polynomialPencilOperator H).charpoly=C B⁻¹.det*H.det := by
  let A : Matrix n n K := fun r s => (H r s).coeff 0
  let B : Matrix n n K := fun r s => (H r s).coeff 1
  change (Matrix.toLin' (-B⁻¹*A)).charpoly=C B⁻¹.det*H.det
  rw [matrix_toLin_charpoly,affine_ratio_charpoly A B B⁻¹
    (Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hd))]
  rw [affineMatrixPencil_coefficients H hH]

theorem polynomial_pencil_eigenvalue_det_root (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hd : Matrix.det (fun r s => (H r s).coeff 1)≠0)
    (a : K) (ha : (polynomialPencilOperator H).HasEigenvalue a) : H.det.eval a=0 := by
  let f := polynomialPencilOperator H
  have hmin : (minpoly K f).eval a=0 := Module.End.isRoot_of_hasEigenvalue ha
  obtain ⟨p,hp⟩ := LinearMap.minpoly_dvd_charpoly f
  have hchar : f.charpoly.eval a=0 := by rw [hp,eval_mul,hmin,zero_mul]
  have he := polynomialPencilOperator_charpoly H hH hd
  have hzero := congrArg (Polynomial.eval a) he
  rw [hchar,eval_mul,eval_C] at hzero
  let B : Matrix n n K := fun r s => (H r s).coeff 1
  have hi : B⁻¹.det≠0 := isUnit_iff_ne_zero.mp
    (Matrix.isUnit_nonsing_inv_det B (isUnit_iff_ne_zero.mpr hd))
  exact (mul_eq_zero.mp hzero.symm).resolve_left hi

end FD56
