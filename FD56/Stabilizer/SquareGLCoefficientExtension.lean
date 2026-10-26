/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericRows
import FD56.LinearAlgebra.StateVariableDescent
import FD56.LinearAlgebra.GenericResonantColumn

/-! Split the original four coefficient families into row coefficients and
independent state coefficients, then extend the original generic field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K L n : Type*} [Field K] [Field L]

def squareAffineVariableSplit (n : Type*) :
    (MatrixParameters n n ⊕ MatrixParameters n n) ≃
      (((n × n) ⊕ (n × n)) ⊕ ((n × n) ⊕ (n × n))) where
  toFun
    | .inl (.inl x) => .inr (.inl x)
    | .inl (.inr x) => .inl (.inl x)
    | .inr (.inl x) => .inr (.inr x)
    | .inr (.inr x) => .inl (.inr x)
  invFun
    | .inl (.inl x) => .inl (.inr x)
    | .inl (.inr x) => .inr (.inr x)
    | .inr (.inl x) => .inl (.inl x)
    | .inr (.inr x) => .inr (.inl x)
  left_inv x := by rcases x with (x|x) | (x|x) <;> rfl
  right_inv x := by rcases x with (x|x) | (x|x) <;> rfl

def squareRowCoefficientMap (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) :
    MvPolynomial (MatrixParameters n n ⊕ MatrixParameters n n) K →+*
      MvPolynomial ((n × n) ⊕ (n × n)) L :=
  (stateCoefficientMap phi).comp (MvPolynomial.rename (squareAffineVariableSplit n)).toRingHom

theorem squareRowCoefficientMap_injective
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi) :
    Function.Injective (squareRowCoefficientMap phi) :=
  (stateCoefficientMap_injective phi hphi).comp
    (MvPolynomial.rename_injective _ (squareAffineVariableSplit n).injective)

theorem squareRowCoefficientMap_M0 (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (ij : n × n) :
    squareRowCoefficientMap phi (MvPolynomial.X (.inl (.inl ij))) = MvPolynomial.X (.inl ij) := by
  simp [squareRowCoefficientMap,squareAffineVariableSplit,stateCoefficientMap_output]

theorem squareRowCoefficientMap_M1 (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (ij : n × n) :
    squareRowCoefficientMap phi (MvPolynomial.X (.inr (.inl ij))) = MvPolynomial.X (.inr ij) := by
  simp [squareRowCoefficientMap,squareAffineVariableSplit,stateCoefficientMap_output]

theorem squareRowCoefficientMap_P0 (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (ij : n × n) :
    squareRowCoefficientMap phi (MvPolynomial.X (.inl (.inr ij))) =
      MvPolynomial.C (phi (MvPolynomial.X (.inl ij))) := by
  simp [squareRowCoefficientMap,squareAffineVariableSplit,stateCoefficientMap_state]

theorem squareRowCoefficientMap_P1 (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (ij : n × n) :
    squareRowCoefficientMap phi (MvPolynomial.X (.inr (.inr ij))) =
      MvPolynomial.C (phi (MvPolynomial.X (.inr ij))) := by
  simp [squareRowCoefficientMap,squareAffineVariableSplit,stateCoefficientMap_state]

abbrev SquareGLIndependentField (L n : Type*) [Field L] :=
  FractionRing (MvPolynomial ((n × n) ⊕ (n × n)) L)

def squareGenericFieldMap (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L)
    (hphi : Function.Injective phi) :
    AffineCoefficientField K (MatrixParameters n n) →+* SquareGLIndependentField L n :=
  IsFractionRing.lift (g :=
    (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)).comp
      (squareRowCoefficientMap phi)) ((IsFractionRing.injective
    (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)).comp
      (squareRowCoefficientMap_injective phi hphi))

theorem squareGenericFieldMap_variable
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi)
    (i : MatrixParameters n n ⊕ MatrixParameters n n) :
    squareGenericFieldMap phi hphi
      (algebraMap (MvPolynomial (MatrixParameters n n ⊕ MatrixParameters n n) K)
        (AffineCoefficientField K (MatrixParameters n n)) (MvPolynomial.X i)) =
      algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)
        (squareRowCoefficientMap phi (MvPolynomial.X i)) :=
  IsFractionRing.lift_algebraMap _ _

theorem squareGenericFieldMap_state_pencil
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi) :
    (genericAffineSquare K n n).map (Polynomial.mapRingHom (squareGenericFieldMap phi hphi)) =
      affineMatrixPencil
        (independentMatrixConstant.map (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L)
          (SquareGLIndependentField L n)))
        (independentMatrixLeading.map (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L)
          (SquareGLIndependentField L n))) := by
  funext i j
  simp [genericAffineSquare,universalSquare,affineParameterMap,affineMatrixPencil,
    squareGenericFieldMap_variable,squareRowCoefficientMap_M0,squareRowCoefficientMap_M1,
    independentMatrixConstant,independentMatrixLeading]

theorem squareGenericFieldMap_row_pencil
    (phi : MvPolynomial ((n × n) ⊕ (n × n)) K →+* L) (hphi : Function.Injective phi) :
    (genericAffineRows K n n).map (Polynomial.mapRingHom (squareGenericFieldMap phi hphi)) =
      affineMatrixPencil
        ((Matrix.of fun i j => phi (MvPolynomial.X (.inl (i,j))) : Matrix n n L).map
          ((algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)).comp MvPolynomial.C))
        ((Matrix.of fun i j => phi (MvPolynomial.X (.inr (i,j))) : Matrix n n L).map
          ((algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) L) (SquareGLIndependentField L n)).comp MvPolynomial.C)) := by
  funext i j
  simp [genericAffineRows,universalRows,affineParameterMap,affineMatrixPencil,
    squareGenericFieldMap_variable,squareRowCoefficientMap_P0,squareRowCoefficientMap_P1]

end FD56
