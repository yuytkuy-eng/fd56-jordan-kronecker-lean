/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.FieldSLKirillovKernel
import FD56.Stabilizer.FieldSLMatrix
import FD56.Stabilizer.GLSimplePoleKernel

/-! A nonsingular GL Kirillov form restricts to an SL form of nullity one. -/

noncomputable section
namespace FD56
open Matrix
variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem fieldSLRadical_finrank_of_gl_det_ne_zero [Nonempty n]
    (M : Matrix n n K) (P : Matrix m n K) (hd : (glKirillovMatrix M P).det≠0) :
    Module.finrank K (fieldSLRadical M P)=1 := by
  have hi : Function.Injective (glKirillovMatrix M P).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hd))
  have hgl : Module.finrank K (glStabilizerSpace M P)=0 := by
    rw [← glKirillovMatrix_field_finrank,LinearMap.ker_eq_bot.mpr hi,finrank_bot]
  have htrace (z : glStabilizerSpace M P) : Matrix.trace z.val.1=0 := by
    have hz : z.val=0 := (Submodule.finrank_eq_zero.mp hgl).le z.property
    simp [hz]
  rw [fieldSLRadical_finrank M P htrace,hgl,zero_add]

theorem slKirillovMatrix_nullity_of_gl_det_ne_zero
    (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) (hd : (glKirillovMatrix M P).det≠0) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (slKirillovMatrix M P i₀)))=1 := by
  letI : Nonempty n := ⟨i₀⟩
  rw [slKirillovMatrix_field_finrank,fieldSLRadical_finrank_of_gl_det_ne_zero M P hd]

theorem slEquationMatrix_nullity_of_gl_det_ne_zero
    (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) (hd : (glKirillovMatrix M P).det≠0) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀)))=1 := by
  letI : Nonempty n := ⟨i₀⟩
  rw [slEquationMatrix_field_finrank,fieldSLRadical_finrank_of_gl_det_ne_zero M P hd]

end FD56
