/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericDimension
import FD56.Stabilizer.ObservabilityCovariance
import FD56.LinearAlgebra.GenericAffineDivisors
import FD56.LinearAlgebra.PolynomialGCDInvariance
import Mathlib.LinearAlgebra.Matrix.Transvection

/-! Elementary output substitutions on the universal matrix coefficient ring. -/

noncomputable section
namespace FD56
open MvPolynomial Matrix
variable {R n m : Type*} [CommRing R] [DecidableEq m]

def elementaryOutputHom (i j : m) (c : R) :
    MvPolynomial (MatrixParameters n m) R →ₐ[R] MvPolynomial (MatrixParameters n m) R :=
  aeval (Sum.elim (fun a => X (Sum.inl a))
    (fun a => if a.1 = i then X (Sum.inr a) + C c * X (Sum.inr (j,a.2))
      else X (Sum.inr a)))

theorem elementaryOutputHom_comp_neg (i j : m) (hij : i ≠ j) (c : R) :
    (elementaryOutputHom (n := n) i j c).comp (elementaryOutputHom i j (-c)) =
      AlgHom.id R _ := by
  ext a
  cases a with
  | inl a => simp [elementaryOutputHom]
  | inr a =>
    by_cases ha : a.1 = i
    · simp [elementaryOutputHom, ha, hij.symm, map_add, map_mul]
    · simp [elementaryOutputHom, ha]

def elementaryOutputEquiv (i j : m) (hij : i ≠ j) (c : R) :
    MvPolynomial (MatrixParameters n m) R ≃ₐ[R] MvPolynomial (MatrixParameters n m) R :=
  AlgEquiv.ofAlgHom (elementaryOutputHom i j c) (elementaryOutputHom i j (-c))
    (elementaryOutputHom_comp_neg i j hij c)
    (by simpa using elementaryOutputHom_comp_neg (n := n) i j hij (-c))

theorem elementaryOutputEquiv_square (i j : m) (hij : i ≠ j) (c : R) (a b : n) :
    elementaryOutputEquiv i j hij c ((universalSquare R n m) a b) =
      (universalSquare R n m) a b := by
  simp [elementaryOutputEquiv, elementaryOutputHom, universalSquare]

theorem elementaryOutputEquiv_rows (i j : m) (hij : i ≠ j) (c : R) (a : m) (b : n) :
    elementaryOutputEquiv i j hij c ((universalRows R n m) a b) =
      if a = i then (universalRows R n m) a b + C c * (universalRows R n m) j b
      else (universalRows R n m) a b := by
  simp [elementaryOutputEquiv, elementaryOutputHom, universalRows]

def elementaryOutputParameter (i j : m) (hij : i ≠ j) :
    Polynomial (MvPolynomial (MatrixParameters n m) R) ≃+*
      Polynomial (MvPolynomial (MatrixParameters n m) R) :=
  polynomialVariableSwap.trans
    ((elementaryOutputEquiv i j hij (Polynomial.X : Polynomial R)).toRingEquiv.trans
      polynomialVariableSwap.symm)

theorem elementaryOutputParameter_square (i j : m) (hij : i ≠ j) (a b : n) :
    elementaryOutputParameter i j hij (Polynomial.C ((universalSquare R n m) a b)) =
      Polynomial.C ((universalSquare R n m) a b) := by
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X
      (polynomialVariableSwap (Polynomial.C (X (Sum.inl (a,b)))))) = _
  rw [polynomialVariableSwap_C_X]
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X ((universalSquare (Polynomial R) n m) a b)) = _
  rw [elementaryOutputEquiv_square]
  apply polynomialVariableSwap.injective
  simp only [RingEquiv.apply_symm_apply, universalSquare, polynomialVariableSwap_C_X]

theorem elementaryOutputParameter_rows (i j : m) (hij : i ≠ j) (a : m) (b : n) :
    elementaryOutputParameter i j hij (Polynomial.C ((universalRows R n m) a b)) =
      if a = i then Polynomial.C ((universalRows R n m) a b) +
        Polynomial.X * Polynomial.C ((universalRows R n m) j b)
      else Polynomial.C ((universalRows R n m) a b) := by
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X
      (polynomialVariableSwap (Polynomial.C (X (Sum.inr (a,b)))))) = _
  rw [polynomialVariableSwap_C_X]
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X ((universalRows (Polynomial R) n m) a b)) = _
  rw [elementaryOutputEquiv_rows]
  by_cases h : a = i
  · simp only [h, ite_true]
    apply polynomialVariableSwap.injective
    simp only [RingEquiv.apply_symm_apply, map_add, map_mul, universalRows,
      polynomialVariableSwap_C_X, polynomialVariableSwap_X]
  · simp only [h, ite_false]
    apply polynomialVariableSwap.injective
    simp only [RingEquiv.apply_symm_apply, universalRows, polynomialVariableSwap_C_X]

theorem elementaryOutputParameter_X (i j : m) (hij : i ≠ j) :
    elementaryOutputParameter (R := R) (n := n) i j hij Polynomial.X = Polynomial.X := by
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X (polynomialVariableSwap Polynomial.X)) = _
  rw [polynomialVariableSwap_X]
  have hc : elementaryOutputEquiv i j hij (Polynomial.X : Polynomial R)
      (C Polynomial.X : MvPolynomial (MatrixParameters n m) (Polynomial R)) = C Polynomial.X := by
    simp [elementaryOutputEquiv, elementaryOutputHom]
  rw [hc]
  apply polynomialVariableSwap.injective
  simp only [RingEquiv.apply_symm_apply, polynomialVariableSwap_X]

theorem elementaryOutputParameter_C_C (i j : m) (hij : i ≠ j) (r : R) :
    elementaryOutputParameter (n := n) i j hij (Polynomial.C (C r)) = Polynomial.C (C r) := by
  have hs : polynomialVariableSwap (Polynomial.C (C r : MvPolynomial (MatrixParameters n m) R)) =
      C (Polynomial.C r) := by
    change optionEquivRight R (MatrixParameters n m)
      ((optionEquivLeft R (MatrixParameters n m)).symm (Polynomial.C (C r))) = _
    rw [← optionEquivLeft_C, AlgEquiv.symm_apply_apply]
    exact optionEquivRight_C R (MatrixParameters n m) r
  change polynomialVariableSwap.symm
    (elementaryOutputEquiv i j hij Polynomial.X (polynomialVariableSwap (Polynomial.C (C r)))) = _
  rw [hs]
  have hc : elementaryOutputEquiv i j hij (Polynomial.X : Polynomial R)
      (C (Polynomial.C r) : MvPolynomial (MatrixParameters n m) (Polynomial R)) =
      C (Polynomial.C r) := by simp [elementaryOutputEquiv, elementaryOutputHom]
  rw [hc]
  exact polynomialVariableSwap.symm_apply_eq.mpr hs.symm

theorem elementaryOutputParameter_eval_zero (i j : m) (hij : i ≠ j)
    (f : MvPolynomial (MatrixParameters n m) R) :
    (elementaryOutputParameter i j hij (Polynomial.C f)).eval 0 = f := by
  have he : (Polynomial.evalRingHom (0 : MvPolynomial (MatrixParameters n m) R)).comp
      ((elementaryOutputParameter i j hij).toRingHom.comp Polynomial.C) = RingHom.id _ := by
    apply MvPolynomial.ringHom_ext
    · intro r
      change (elementaryOutputParameter i j hij (Polynomial.C (C r))).eval 0 = C r
      rw [elementaryOutputParameter_C_C, Polynomial.eval_C]
    · intro a
      cases a with
      | inl a =>
        change (elementaryOutputParameter i j hij
          (Polynomial.C ((universalSquare R n m) a.1 a.2))).eval 0 = _
        rw [elementaryOutputParameter_square, Polynomial.eval_C]
        rfl
      | inr a =>
        change (elementaryOutputParameter i j hij
          (Polynomial.C ((universalRows R n m) a.1 a.2))).eval 0 = _
        rw [elementaryOutputParameter_rows]
        split_ifs <;> simp [Polynomial.eval_add, Polynomial.eval_mul, universalRows]
  exact DFunLike.congr_fun he f

theorem elementaryOutputParameter_map_square (i j : m) (hij : i ≠ j) :
    ((universalSquare R n m).map Polynomial.C).map
      (elementaryOutputParameter i j hij).toRingHom = (universalSquare R n m).map Polynomial.C := by
  apply Matrix.ext
  intro a b
  exact elementaryOutputParameter_square (R := R) i j hij a b

theorem elementaryOutputParameter_map_rows [Fintype m] (i j : m) (hij : i ≠ j) :
    ((universalRows R n m).map Polynomial.C).map
      (elementaryOutputParameter i j hij).toRingHom =
        Matrix.transvection i j Polynomial.X * (universalRows R n m).map Polynomial.C := by
  apply Matrix.ext
  intro a b
  change elementaryOutputParameter i j hij (Polynomial.C ((universalRows R n m) a b)) = _
  rw [elementaryOutputParameter_rows]
  by_cases ha : a = i
  · subst a
    simp [Matrix.transvection, Matrix.add_mul]
  · simp [ha, Matrix.transvection, Matrix.add_mul]

omit [DecidableEq m] in
theorem universal_observability_minor_constant [Fintype n] [DecidableEq n]
    (q : ℕ) (r : n → Fin q × m) :
    Polynomial.C (((observabilityMatrix (universalSquare R n m) (universalRows R n m) q).submatrix r id).det) =
      ((observabilityMatrix ((universalSquare R n m).map Polynomial.C)
        ((universalRows R n m).map Polynomial.C) q).submatrix r id).det := by
  rw [RingHom.map_det]
  congr 1
  apply Matrix.ext
  intro a b
  exact congrArg (fun A => A (r a) b)
    (observabilityMatrix_map Polynomial.C (universalSquare R n m) (universalRows R n m) q)

theorem elementaryOutputParameter_minor_divisors [Fintype n] [DecidableEq n] [Fintype m]
    (i j : m) (hij : i ≠ j) (q : ℕ) (d : Polynomial (MvPolynomial (MatrixParameters n m) R)) :
    (∀ r : n → Fin q × m, d ∣ elementaryOutputParameter i j hij
      (Polynomial.C (((observabilityMatrix (universalSquare R n m) (universalRows R n m) q).submatrix r id).det))) ↔
      (∀ r : n → Fin q × m, d ∣ Polynomial.C
        (((observabilityMatrix (universalSquare R n m) (universalRows R n m) q).submatrix r id).det)) := by
  simp_rw [universal_observability_minor_constant]
  change (∀ r : n → Fin q × m, d ∣ (elementaryOutputParameter i j hij).toRingHom
    (((observabilityMatrix ((universalSquare R n m).map Polynomial.C)
      ((universalRows R n m).map Polynomial.C) q).submatrix r id).det)) ↔ _
  simp_rw [observabilityMatrix_minor_map, elementaryOutputParameter_map_square,
    elementaryOutputParameter_map_rows]
  apply observabilityMatrix_output_change_minor_divisors _ _
    (Matrix.transvection i j Polynomial.X) (Matrix.transvection i j (-Polynomial.X))
  rw [Matrix.transvection_mul_transvection_same i j hij, neg_add_cancel, Matrix.transvection_zero]

/-- The universal observability-minor gcd is fixed by an elementary output change. -/
theorem elementaryOutputParameter_gcd_invariant [Fintype n] [DecidableEq n] [Fintype m]
    [IsDomain R] [NormalizedGCDMonoid (MvPolynomial (MatrixParameters n m) R)]
    [NormalizedGCDMonoid (Polynomial (MvPolynomial (MatrixParameters n m) R))]
    (i j : m) (hij : i ≠ j) (q : ℕ) :
    elementaryOutputParameter i j hij (Polynomial.C
      (observabilityMinorGCD (universalSquare R n m) (universalRows R n m) q)) =
      Polynomial.C (observabilityMinorGCD (universalSquare R n m) (universalRows R n m) q) := by
  apply finite_gcd_parameter_invariant
  · intro d
    exact elementaryOutputParameter_minor_divisors i j hij q d
  · intro a
    exact elementaryOutputParameter_eval_zero i j hij a

end FD56
