/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.RingTheory.Derivation.MapCoeffs
import FD56.LinearAlgebra.MatrixDeterminantDerivation

/-! Coefficient derivations fix the polynomial variable and preserve degree bounds. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]

def polynomialCoefficientDerivation (D : Derivation R A A) : Derivation R A[X] A[X] :=
  PolynomialModule.equivPolynomialSelf.compDer D.mapCoeffs

theorem polynomialCoefficientDerivation_coeff (D : Derivation R A A) (p : A[X]) (i : ℕ) :
    (polynomialCoefficientDerivation D p).coeff i = D (p.coeff i) := rfl

theorem polynomialCoefficientDerivation_natDegree_le (D : Derivation R A A) (p : A[X]) :
    (polynomialCoefficientDerivation D p).natDegree ≤ p.natDegree := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro i hi
  rw [polynomialCoefficientDerivation_coeff,Polynomial.coeff_eq_zero_of_natDegree_lt hi,
    map_zero]

theorem polynomialCoefficientDerivation_degree_bound (D : Derivation R A A)
    (p : A[X]) (d : ℕ) (hp : p.natDegree ≤ d) :
    (polynomialCoefficientDerivation D p).natDegree ≤ d :=
  (polynomialCoefficientDerivation_natDegree_le D p).trans hp

theorem polynomialCoefficientDerivation_C (D : Derivation R A A) (a : A) :
    polynomialCoefficientDerivation D (C a) = C (D a) := by
  ext i
  simp only [polynomialCoefficientDerivation_coeff,Polynomial.coeff_C]
  split_ifs <;> simp

theorem polynomialCoefficientDerivation_X (D : Derivation R A A) :
    polynomialCoefficientDerivation D (X : A[X]) = 0 := by
  ext i
  simp only [polynomialCoefficientDerivation_coeff,Polynomial.coeff_X,Polynomial.coeff_zero]
  split_ifs <;> simp

end FD56
