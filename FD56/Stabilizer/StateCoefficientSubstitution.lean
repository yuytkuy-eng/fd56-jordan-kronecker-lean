/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDimension
import Mathlib.Algebra.MvPolynomial.Equiv
import FD56.Stabilizer.ObservabilityCovariance
import Mathlib.RingTheory.Polynomial.Basic

/-! State-coordinate substitutions on the universal matrix coefficient ring. -/

noncomputable section
namespace FD56
open Matrix MvPolynomial
variable {R n m : Type*} [CommRing R] [Fintype n] [DecidableEq n]

def stateCoefficientHom (S T : Matrix n n R) :
    MvPolynomial (MatrixParameters n m) R →ₐ[R] MvPolynomial (MatrixParameters n m) R :=
  aeval (Sum.elim
    (fun ij : n × n => (T.map C * universalSquare R n m * S.map C : Matrix n n (MvPolynomial (MatrixParameters n m) R)) ij.1 ij.2)
    (fun ij : m × n => (universalRows R n m * S.map C : Matrix m n (MvPolynomial (MatrixParameters n m) R)) ij.1 ij.2))

omit [DecidableEq n] in
theorem stateCoefficientHom_square (S T : Matrix n n R) :
    (universalSquare R n m).map (stateCoefficientHom S T).toRingHom =
      T.map C * universalSquare R n m * S.map C := by
  ext i j : 1
  simp [universalSquare, stateCoefficientHom]

omit [DecidableEq n] in
theorem stateCoefficientHom_rows (S T : Matrix n n R) :
    (universalRows R n m).map (stateCoefficientHom S T).toRingHom =
      universalRows R n m * S.map C := by
  ext i j : 1
  simp [universalRows, stateCoefficientHom]

omit [DecidableEq n] in
theorem stateCoefficientHom_constants {a b : Type*} (S T : Matrix n n R) (A : Matrix a b R) :
    (A.map C).map (stateCoefficientHom (m := m) S T).toRingHom = A.map C := by
  ext i j : 1
  simp [stateCoefficientHom]

theorem stateCoefficientHom_comp_inverse (S T : Matrix n n R)
    (hST : S * T = 1) (hTS : T * S = 1) :
    (stateCoefficientHom (m := m) S T).comp (stateCoefficientHom T S) = AlgHom.id R _ := by
  have hSc : S.map (C : R →+* MvPolynomial (MatrixParameters n m) R) * T.map C = 1 := by
    rw [← Matrix.map_mul, hST]
    exact map_one C.mapMatrix
  have hTc : T.map (C : R →+* MvPolynomial (MatrixParameters n m) R) * S.map C = 1 := by
    rw [← Matrix.map_mul, hTS]
    exact map_one C.mapMatrix
  have hM : ((universalSquare R n m).map (stateCoefficientHom T S).toRingHom).map
      (stateCoefficientHom S T).toRingHom = universalSquare R n m := by
    rw [stateCoefficientHom_square, Matrix.map_mul, Matrix.map_mul,
      stateCoefficientHom_constants, stateCoefficientHom_constants, stateCoefficientHom_square]
    calc
      _ = (S.map C * T.map C) * universalSquare R n m * (S.map C * T.map C) := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSc]; simp
  have hP : ((universalRows R n m).map (stateCoefficientHom T S).toRingHom).map
      (stateCoefficientHom S T).toRingHom = universalRows R n m := by
    rw [stateCoefficientHom_rows, Matrix.map_mul, stateCoefficientHom_constants,
      stateCoefficientHom_rows, Matrix.mul_assoc, hSc, Matrix.mul_one]
  ext i : 1
  cases i with
  | inl ij => exact congrArg (fun A => A ij.1 ij.2) hM
  | inr ij => exact congrArg (fun A => A ij.1 ij.2) hP

def stateCoefficientEquiv (S T : Matrix n n R) (hST : S * T = 1) (hTS : T * S = 1) :
    MvPolynomial (MatrixParameters n m) R ≃ₐ[R] MvPolynomial (MatrixParameters n m) R :=
  AlgEquiv.ofAlgHom (stateCoefficientHom S T) (stateCoefficientHom T S)
    (stateCoefficientHom_comp_inverse S T hST hTS)
    (stateCoefficientHom_comp_inverse T S hTS hST)

theorem universal_observability_gcd_state_semi_invariant [Fintype m] [IsDomain R]
    [NormalizedGCDMonoid (MvPolynomial (MatrixParameters n m) R)]
    (S T : Matrix n n R) (hST : S * T = 1) (hTS : T * S = 1) (q : ℕ) :
    Associated (stateCoefficientEquiv (m := m) S T hST hTS
      (observabilityMinorGCD (universalSquare R n m) (universalRows R n m) q))
      (observabilityMinorGCD (universalSquare R n m) (universalRows R n m) q) := by
  let U : (Matrix n n (MvPolynomial (MatrixParameters n m) R))ˣ :=
    { val := S.map C
      inv := T.map C
      val_inv := by rw [← Matrix.map_mul, hST]; exact map_one C.mapMatrix
      inv_val := by rw [← Matrix.map_mul, hTS]; exact map_one C.mapMatrix }
  have h := observabilityMinorGCD_map_associated
    (stateCoefficientEquiv (m := m) S T hST hTS).toRingEquiv
    (universalSquare R n m) (universalRows R n m) q
  change Associated _ (observabilityMinorGCD
    ((universalSquare R n m).map (stateCoefficientHom S T).toRingHom)
    ((universalRows R n m).map (stateCoefficientHom S T).toRingHom) q) at h
  rw [stateCoefficientHom_square, stateCoefficientHom_rows] at h
  exact h.trans (observabilityMinorGCD_state_change
    (universalSquare R n m) (universalRows R n m) U q)

end FD56
