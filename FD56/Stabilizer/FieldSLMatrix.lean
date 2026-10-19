/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SLMatrix
import FD56.Stabilizer.FieldRadical

/-! The SL constraint matrix commutes with coefficient homomorphisms and
has exactly the full field-valued SL radical as its kernel. -/

noncomputable section
namespace FD56
open Matrix

theorem stabilizerResidual_map {R S n m : Type*} [CommRing R] [CommRing S]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (φ : R →+* S) (M : Matrix n n R) (P : Matrix m n R)
    (z : Matrix n n R × Matrix n m R) :
    stabilizerResidual (M.map φ) (P.map φ) (z.1.map φ, z.2.map φ) =
      (stabilizerResidual M P z).map φ := by
  ext i j
  simp [stabilizerResidual, Matrix.mul_apply, map_sum]

theorem slEquationLinearMap_map {R S n m : Type*} [CommRing R] [CommRing S]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (φ : R →+* S) (M : Matrix n n R) (P : Matrix m n R) (i₀ : n)
    (v : SLInput n m → R) :
    (fun a => φ (slEquationLinearMap M P i₀ v a)) =
      slEquationLinearMap (M.map φ) (P.map φ) i₀ (fun b => φ (v b)) := by
  funext a
  rcases a with u | ij | ij
  · cases u
    simp [slEquationLinearMap, constraintOutputEquiv, slConstraintMap,
      matrixPairEquiv, Matrix.trace, Matrix.diag, map_sum]
  · simp [slEquationLinearMap, constraintOutputEquiv, slConstraintMap,
      matrixPairEquiv, Matrix.mul_apply, map_sum]
  · by_cases h : ij.1 = ij.2 <;> simp [slEquationLinearMap, constraintOutputEquiv, slConstraintMap,
      matrixPairEquiv, stabilizerResidual, scalarCorrectionResidual, Matrix.mul_apply,
      Matrix.one_apply, map_sum, h]

theorem slEquationMatrix_map {R S n m : Type*} [CommRing R] [CommRing S]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (φ : R →+* S) (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (slEquationMatrix M P i₀).map φ = slEquationMatrix (M.map φ) (P.map φ) i₀ := by
  ext a b
  have h := congrFun (slEquationLinearMap_map φ M P i₀ (fun j => if j = b then 1 else 0)) a
  simpa [slEquationMatrix, LinearMap.toMatrix'_apply] using h

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

theorem slConstraintMap_eq_fieldSLRadical (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (X : Matrix n n K) (U : Matrix n m K) :
    slConstraintMap M P i₀ (X, U) = 0 ↔ (X, U) ∈ fieldSLRadical M P := by
  letI : Nonempty n := ⟨i₀⟩
  rw [fieldSLRadical_iff_equations]
  change (Matrix.trace X, P * X, scalarCorrectionResidual i₀ (M * X - X * M - U * P)) = 0 ↔ _
  simp only [Prod.mk_eq_zero, scalarCorrectionResidual_eq_zero_iff]
  constructor
  · rintro ⟨ht, hp, c, hc⟩
    exact ⟨ht, hp, c, (sub_eq_iff_eq_add.mp hc).trans (add_comm _ _)⟩
  · rintro ⟨ht, hp, c, hc⟩
    refine ⟨ht, hp, c, ?_⟩
    rw [hc, add_sub_cancel_left]

theorem slEquationMatrix_field_kernel_iff (M : Matrix n n K) (P : Matrix m n K)
    (i₀ : n) (v : SLInput n m → K) :
    slEquationMatrix M P i₀ *ᵥ v = 0 ↔ matrixPairEquiv K K n m v ∈ fieldSLRadical M P := by
  change Matrix.toLin' (LinearMap.toMatrix' (slEquationLinearMap M P i₀)) v = 0 ↔ _
  rw [Matrix.toLin'_toMatrix']
  change constraintOutputEquiv K n m (slConstraintMap M P i₀ (matrixPairEquiv K K n m v)) = 0 ↔ _
  rw [(constraintOutputEquiv K n m).map_eq_zero_iff]
  exact slConstraintMap_eq_fieldSLRadical M P i₀ _ _

def fieldSLKernelEquiv (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) :
    LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀)) ≃ₗ[K] fieldSLRadical M P where
  toFun v := ⟨matrixPairEquiv K K n m v.val, (slEquationMatrix_field_kernel_iff M P i₀ v.val).mp v.property⟩
  invFun z := ⟨(matrixPairEquiv K K n m).symm z.val, by
    apply (slEquationMatrix_field_kernel_iff M P i₀ _).mpr
    simp only [LinearEquiv.apply_symm_apply]
    exact z.property⟩
  left_inv v := by apply Subtype.ext; exact (matrixPairEquiv K K n m).left_inv v.val
  right_inv z := by apply Subtype.ext; exact (matrixPairEquiv K K n m).right_inv z.val
  map_add' v w := by apply Subtype.ext; rfl
  map_smul' c v := by apply Subtype.ext; rfl

theorem slEquationMatrix_field_finrank (M : Matrix n n K) (P : Matrix m n K) (i₀ : n) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' (slEquationMatrix M P i₀))) =
      Module.finrank K (fieldSLRadical M P) :=
  (fieldSLKernelEquiv M P i₀).finrank_eq

theorem slEquationMatrix_specialized_finrank {R : Type*} [CommRing R]
    (φ : R →+* K) (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    Module.finrank K (LinearMap.ker (Matrix.toLin' ((slEquationMatrix M P i₀).map φ))) =
      Module.finrank K (fieldSLRadical (M.map φ) (P.map φ)) := by
  rw [slEquationMatrix_map, slEquationMatrix_field_finrank]

end FD56
