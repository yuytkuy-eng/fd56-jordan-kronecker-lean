/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GLObservabilityDeterminant
import FD56.Stabilizer.GenericObservabilitySeparable

/-! The one-output GL determinant is the square of the scalar observability determinant. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem scalar_gl_kirillov_determinant {R : Type*} [CommRing R] [IsDomain R]
    (N : ℕ) (M : Matrix (Fin N) (Fin N) R) (P : Matrix (Fin 1) (Fin N) R)
    (hO : (observabilitySelectedMatrix M P Fin.val (fun _ => 0)).det ≠ 0) :
    (glKirillovMatrix M P).det =
      (observabilitySelectedMatrix M P Fin.val (fun _ => 0)).det ^ 2 := by
  let e : Fin N × Fin 1 ≃ Fin N := Equiv.prodUnique _ _
  have hpow (k : ℕ) : (M.submatrix e e)^k=(M^k).submatrix e e := by
    induction k with
    | zero => simp [Matrix.submatrix_one_equiv]
    | succ k ih => rw [pow_succ,pow_succ,ih,Matrix.submatrix_mul_equiv]
  have ho : observabilityMatrix (M.submatrix e e) (P.submatrix (Equiv.refl _) e) N =
      (observabilitySelectedMatrix M P Fin.val (fun _ => 0)).submatrix e e := by
    ext ⟨i,j⟩ ⟨k,l⟩
    have hj : j=0 := Subsingleton.elim _ _
    simp only [observabilityMatrix,hpow,Matrix.submatrix_mul_equiv,
      observabilitySelectedMatrix,Matrix.submatrix_apply,Equiv.refl_apply]
    simpa only [e,Equiv.prodUnique_apply,hj]
  have hd : (observabilityMatrix (M.submatrix e e) (P.submatrix (Equiv.refl _) e) N).det =
      (observabilitySelectedMatrix M P Fin.val (fun _ => 0)).det := by
    rw [ho,Matrix.det_submatrix_equiv_self]
  cases N with
  | zero => simp [Matrix.det_isEmpty]
  | succ N =>
    have h := glKirillovMatrix_det_observability_ne_zero N
      (M.submatrix e e) (P.submatrix (Equiv.refl _) e) (by rwa [hd])
    rw [glKirillovMatrix_det_reindex,hd] at h
    simpa using h

theorem generic_scalar_gl_kirillov_determinant (K : Type*) [Field K] (N : ℕ) :
    (glKirillovMatrix (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1))).det =
    (observabilitySelectedMatrix (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)) Fin.val (fun _ => 0)).det ^ 2 :=
  scalar_gl_kirillov_determinant N _ _ (generic_scalar_observability_separable K N).2.ne_zero

end FD56
