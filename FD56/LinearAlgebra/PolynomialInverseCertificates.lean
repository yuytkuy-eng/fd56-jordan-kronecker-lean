/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialFamilyDenominators
import Mathlib.FieldTheory.Separable

/-! Polynomial inverse and separability identities descend from a fraction
field after multiplication by one nonzero scalar denominator. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R F a b : Type*} [CommRing R] [IsDomain R] [Field F]
  [Algebra R F] [IsFractionRing R F]
  [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]

theorem polynomial_right_inverse_clear_denominators
    (A : Matrix a b R[X]) (B : Matrix b a F[X])
    (h : A.map (Polynomial.mapRingHom (algebraMap R F))*B=1) :
    ∃ (d : R) (U : Matrix b a R[X]), d≠0 ∧ A*U=C d•1 := by
  let φ := Polynomial.mapRingHom (algebraMap R F)
  obtain ⟨d,w,hd,hw⟩ := polynomial_family_clear_denominators (R:=R)
    (fun i : b × a => B i.1 i.2)
  let U : Matrix b a R[X] := fun i j => w (i,j)
  have hU : U.map φ=C (algebraMap R F d)•B := by
    funext i j
    exact hw (i,j)
  refine ⟨d,U,hd,?_⟩
  apply Matrix.map_injective (Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F))
  change (A*U).map φ=(C d•(1 : Matrix a a R[X])).map φ
  rw [Matrix.map_mul,hU,Matrix.mul_smul,h]
  funext i j
  by_cases hij : i=j <;>
    simp [Matrix.map_apply,Matrix.smul_apply,smul_eq_mul,Matrix.one_apply,φ,hij]

theorem polynomial_left_inverse_clear_denominators
    (A : Matrix a b R[X]) (B : Matrix b a F[X])
    (h : B*A.map (Polynomial.mapRingHom (algebraMap R F))=1) :
    ∃ (d : R) (U : Matrix b a R[X]), d≠0 ∧ U*A=C d•1 := by
  have ht : A.transpose.map (Polynomial.mapRingHom (algebraMap R F))*B.transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_one,Matrix.transpose_map]
      using congrArg Matrix.transpose h
  obtain ⟨d,U,hd,hU⟩ := polynomial_right_inverse_clear_denominators A.transpose B.transpose ht
  refine ⟨d,U.transpose,hd,?_⟩
  simpa only [Matrix.transpose_mul,Matrix.transpose_transpose,Matrix.transpose_smul,
    Matrix.transpose_one] using congrArg Matrix.transpose hU

omit [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b] in
theorem polynomial_separability_clear_denominators (f : R[X])
    (h : (f.map (algebraMap R F)).Separable) :
    ∃ (d : R) (A B : R[X]), d≠0 ∧ A*f+B*f.derivative=C d := by
  obtain ⟨a,b,hab⟩ := (Polynomial.separable_def _).mp h
  obtain ⟨d,w,hd,hw⟩ := polynomial_family_clear_denominators (R:=R) (![a,b] : Fin 2 → F[X])
  have hw0 : (w 0).map (algebraMap R F)=C (algebraMap R F d)*a := by simpa using hw 0
  have hw1 : (w 1).map (algebraMap R F)=C (algebraMap R F d)*b := by simpa using hw 1
  refine ⟨d,w 0,w 1,hd,?_⟩
  apply Polynomial.map_injective (algebraMap R F) (IsFractionRing.injective R F)
  rw [Polynomial.map_add,Polynomial.map_mul,Polynomial.map_mul,hw0,hw1,
    ← Polynomial.derivative_map,Polynomial.map_C]
  calc
    _ = C (algebraMap R F d)*(a*f.map (algebraMap R F)+
      b*(f.map (algebraMap R F)).derivative) := by ring
    _ = _ := by rw [hab,mul_one]

end FD56
