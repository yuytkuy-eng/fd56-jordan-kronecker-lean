/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.InputVariableChange
import FD56.LinearAlgebra.StateVariableDescent
import FD56.LinearAlgebra.GenericMatrixSeparable
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Independent row coefficients can be replaced injectively by their leading
matrix and an independent matrix ratio. -/

noncomputable section
namespace FD56
open Matrix
open scoped BigOperators
variable (K n : Type*) [Field K] [Fintype n] [DecidableEq n]

abbrev GenericRowLeadingField := FractionRing (MvPolynomial (n × n) K)
abbrev GenericRowRatioField := FractionRing (MvPolynomial (n × n) (GenericRowLeadingField K n))

def genericRowLeadingMatrix : Matrix n n (GenericRowLeadingField K n) :=
  (Matrix.mvPolynomialX n n K).map (algebraMap _ _)

theorem genericRowLeadingMatrix_det_ne_zero : (genericRowLeadingMatrix K n).det ≠ 0 := by
  let phi : MvPolynomial (n × n) K →+* GenericRowLeadingField K n := algebraMap _ _
  change (phi.mapMatrix (Matrix.mvPolynomialX n n K)).det ≠ 0
  rw [← phi.map_det]
  exact (map_ne_zero_iff phi (IsFractionRing.injective _ _)).mpr
    (Matrix.det_mvPolynomialX_ne_zero n K)

def genericRowCoefficientSplit :
    MvPolynomial ((n × n) ⊕ (n × n)) K →+*
      MvPolynomial (n × n) (GenericRowLeadingField K n) :=
  (MvPolynomial.map (algebraMap (MvPolynomial (n × n) K) (GenericRowLeadingField K n))).comp
    (MvPolynomial.sumAlgEquiv K (n × n) (n × n)).toRingEquiv.toRingHom

omit [Fintype n] [DecidableEq n] in
theorem genericRowCoefficientSplit_injective : Function.Injective (genericRowCoefficientSplit K n) := by
  have hmap : Function.Injective (MvPolynomial.map
      (algebraMap (MvPolynomial (n × n) K) (GenericRowLeadingField K n)) :
      MvPolynomial (n × n) (MvPolynomial (n × n) K) →
        MvPolynomial (n × n) (GenericRowLeadingField K n)) :=
    MvPolynomial.map_injective _ (IsFractionRing.injective _ _)
  exact hmap.comp (MvPolynomial.sumAlgEquiv K (n × n) (n × n)).injective

omit [Fintype n] [DecidableEq n] in
theorem genericRowCoefficientSplit_constant (i j : n) :
    genericRowCoefficientSplit K n (MvPolynomial.X (.inl (i,j))) = MvPolynomial.X (i,j) := by
  simp [genericRowCoefficientSplit]

omit [Fintype n] [DecidableEq n] in
theorem genericRowCoefficientSplit_leading (i j : n) :
    genericRowCoefficientSplit K n (MvPolynomial.X (.inr (i,j))) =
      MvPolynomial.C (genericRowLeadingMatrix K n i j) := by
  simp [genericRowCoefficientSplit,genericRowLeadingMatrix,Matrix.mvPolynomialX]

def genericRowRatioEmbedding :
    MvPolynomial ((n × n) ⊕ (n × n)) K →+* GenericRowRatioField K n :=
  (algebraMap (MvPolynomial (n × n) (GenericRowLeadingField K n)) (GenericRowRatioField K n)).comp
    ((inputVariableChangeHom (-(genericRowLeadingMatrix K n))).comp (genericRowCoefficientSplit K n))

theorem genericRowRatioEmbedding_injective : Function.Injective (genericRowRatioEmbedding K n) := by
  have hunit : IsUnit (genericRowLeadingMatrix K n).det :=
    isUnit_iff_ne_zero.mpr (genericRowLeadingMatrix_det_ne_zero K n)
  have hST : -(genericRowLeadingMatrix K n) * -(genericRowLeadingMatrix K n)⁻¹ = 1 := by
    rw [neg_mul_neg,Matrix.mul_nonsing_inv _ hunit]
  have hTS : -(genericRowLeadingMatrix K n)⁻¹ * -(genericRowLeadingMatrix K n) = 1 := by
    rw [neg_mul_neg,Matrix.nonsing_inv_mul _ hunit]
  have hvar : Function.Injective (inputVariableChangeHom (m := n) (-(genericRowLeadingMatrix K n))) :=
    inputVariableChangeHom_injective _ _ hST hTS
  intro x y h
  apply genericRowCoefficientSplit_injective K n
  apply hvar
  exact IsFractionRing.injective (MvPolynomial (n × n) (GenericRowLeadingField K n))
    (GenericRowRatioField K n) h

def genericRowRatioMatrix : Matrix n n (GenericRowRatioField K n) :=
  (Matrix.mvPolynomialX n n (GenericRowLeadingField K n)).map (algebraMap _ _)

def genericRowLeadingInRatio : Matrix n n (GenericRowRatioField K n) :=
  (genericRowLeadingMatrix K n).map
    ((algebraMap (MvPolynomial (n × n) (GenericRowLeadingField K n))
      (GenericRowRatioField K n)).comp MvPolynomial.C)

omit [DecidableEq n] in
theorem genericRowRatioEmbedding_constant :
    (fun i j => genericRowRatioEmbedding K n (MvPolynomial.X (.inl (i,j)))) =
      -(genericRowLeadingInRatio K n) * genericRowRatioMatrix K n := by
  let phi : MvPolynomial (n × n) (GenericRowLeadingField K n) →+* GenericRowRatioField K n :=
    algebraMap _ _
  have h := inputVariableChangeHom_matrix_map_neg phi (genericRowLeadingMatrix K n)
  simpa only [genericRowRatioEmbedding,RingHom.comp_apply,genericRowCoefficientSplit_constant]
    using h

omit [DecidableEq n] in
theorem genericRowRatioEmbedding_leading :
    (fun i j => genericRowRatioEmbedding K n (MvPolynomial.X (.inr (i,j)))) =
      genericRowLeadingInRatio K n := by
  ext i j
  simp [genericRowRatioEmbedding,RingHom.comp_apply,genericRowCoefficientSplit_leading,
    inputVariableChangeHom_C,genericRowLeadingInRatio]

theorem genericRowRatioMatrix_separable : (genericRowRatioMatrix K n).charpoly.Separable :=
  generic_matrix_charpoly_separable

end FD56
