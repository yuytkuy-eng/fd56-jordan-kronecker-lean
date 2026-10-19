/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.FieldSLMatrix

/-! A coordinate matrix for the full GL stabilizer equations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R n m : Type*} [CommRing R] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

def glEquationLinearMap (M : Matrix n n R) (P : Matrix m n R) :
    (SLInput n m → R) →ₗ[R] (((m × n) ⊕ (n × n)) → R) where
  toFun v := Sum.elim
    (fun ij => (P * (matrixPairEquiv R R n m v).1) ij.1 ij.2)
    (fun ij => stabilizerResidual M P (matrixPairEquiv R R n m v) ij.1 ij.2)
  map_add' v w := by
    funext ij
    rcases ij with ij | ij <;>
      simp [map_add, Matrix.mul_add]
  map_smul' c v := by
    funext ij
    rcases ij with ij | ij <;>
      simp [map_smul, Matrix.mul_smul]

def glEquationMatrix (M : Matrix n n R) (P : Matrix m n R) :
    Matrix ((m × n) ⊕ (n × n)) (SLInput n m) R :=
  LinearMap.toMatrix' (glEquationLinearMap M P)

theorem glEquationMatrix_kernel_iff (M : Matrix n n R) (P : Matrix m n R)
    (v : SLInput n m → R) :
    glEquationMatrix M P *ᵥ v = 0 ↔
      P * (matrixPairEquiv R R n m v).1 = 0 ∧
      stabilizerResidual M P (matrixPairEquiv R R n m v) = 0 := by
  change Matrix.toLin' (LinearMap.toMatrix' (glEquationLinearMap M P)) v = 0 ↔ _
  rw [Matrix.toLin'_toMatrix']
  constructor
  · intro h
    constructor
    · funext i j
      exact congrFun h (.inl (i,j))
    · funext i j
      exact congrFun h (.inr (i,j))
  · rintro ⟨hp, hm⟩
    funext ij
    rcases ij with ij | ij
    · exact congrFun (congrFun hp ij.1) ij.2
    · exact congrFun (congrFun hm ij.1) ij.2

theorem glEquationMatrix_map {S : Type*} [CommRing S]
    (φ : R →+* S) (M : Matrix n n R) (P : Matrix m n R) :
    (glEquationMatrix M P).map φ = glEquationMatrix (M.map φ) (P.map φ) := by
  ext a b
  rcases a with ij | ij <;>
    simp [glEquationMatrix, LinearMap.toMatrix'_apply, glEquationLinearMap,
      matrixPairEquiv, stabilizerResidual, Matrix.mul_apply, map_sum, apply_ite]

variable {K : Type*} [Field K]

theorem glEquationMatrix_field_kernel_iff (M : Matrix n n K) (P : Matrix m n K)
    (v : SLInput n m → K) :
    glEquationMatrix M P *ᵥ v = 0 ↔ matrixPairEquiv K K n m v ∈ glStabilizerSpace M P := by
  rw [glEquationMatrix_kernel_iff]
  constructor
  · rintro ⟨hp, hm⟩
    exact ⟨hp, sub_eq_zero.mp hm⟩
  · rintro ⟨hp, hm⟩
    exact ⟨hp, sub_eq_zero.mpr hm⟩

def fieldGLKernelEquiv (M : Matrix n n K) (P : Matrix m n K) :
    LinearMap.ker (Matrix.toLin' (glEquationMatrix M P)) ≃ₗ[K] glStabilizerSpace M P where
  toFun v := ⟨matrixPairEquiv K K n m v.val, (glEquationMatrix_field_kernel_iff M P v.val).mp v.property⟩
  invFun z := ⟨(matrixPairEquiv K K n m).symm z.val, by
    apply (glEquationMatrix_field_kernel_iff M P _).mpr
    simp only [LinearEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv v := by apply Subtype.ext; exact (matrixPairEquiv K K n m).left_inv v.val
  right_inv z := by apply Subtype.ext; exact (matrixPairEquiv K K n m).right_inv z.val
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

theorem glEquationMatrix_field_finrank (M : Matrix n n K) (P : Matrix m n K) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (glEquationMatrix M P))) =
      Module.finrank K (glStabilizerSpace M P) := (fieldGLKernelEquiv M P).finrank_eq

end FD56
