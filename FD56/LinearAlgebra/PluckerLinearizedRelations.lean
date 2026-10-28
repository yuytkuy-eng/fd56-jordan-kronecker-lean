/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.TwoColumnPluckerTangent
import FD56.LinearAlgebra.PolynomialCoefficientDerivation

/-! Differentiating the three-term Plucker equations gives all six-term
linearized equations, over any commutative coefficient ring. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {R n : Type*} [CommRing R]

def pluckerQuadraticRelation (F : Matrix n n R) (i j k l : n) : R :=
  F i j*F k l-F i k*F j l+F i l*F j k

def pluckerLinearizedRelation (F H : Matrix n n R) (i j k l : n) : R :=
  F i j*H k l-F i k*H j l+F i l*H j k+
    F j k*H i l-F j l*H i k+F k l*H i j

theorem scaled_wedge_plucker_relation (c : R) (u v : n → R) (i j k l : n) :
    pluckerQuadraticRelation (c • twoColumnWedge u v) i j k l=0 := by
  dsimp [pluckerQuadraticRelation,twoColumnWedge]
  ring

theorem plucker_relation_derivation {B : Type*} [CommRing B] [Algebra B R]
    (D : Derivation B R R) (F : Matrix n n R)
    (hF : ∀ i j k l, pluckerQuadraticRelation F i j k l=0) (i j k l : n) :
    pluckerLinearizedRelation F (fun a b => D (F a b)) i j k l=0 := by
  have h := congrArg D (hF i j k l)
  simp only [pluckerQuadraticRelation,map_add,map_sub,map_zero,Derivation.leibniz] at h
  dsimp [pluckerLinearizedRelation]
  simp only [smul_eq_mul] at h
  linear_combination h

theorem plucker_relation_coefficient_derivation {K L : Type*}
    [Field K] [Field L] [Algebra K L]
    (D : Derivation K L L) (F : Matrix n n L[X])
    (hF : ∀ i j k l, pluckerQuadraticRelation F i j k l=0) (i j k l : n) :
    pluckerLinearizedRelation F
      (fun a b => polynomialCoefficientDerivation D (F a b)) i j k l=0 :=
  plucker_relation_derivation (polynomialCoefficientDerivation D) F hF i j k l

end FD56
