/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ThreeColumnEqualNormalization
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.Algebra.MvPolynomial.Eval

/-! Universal equal-degree three-column frames and a nonzero leading pivot. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false

abbrev ThreeColumnCoefficientIndex (n : Type*) (h : ℕ) := n × Fin 3 × Fin (h+1)
abbrev ThreeColumnCoefficientRing (K n : Type*) [Field K] (h : ℕ) :=
  MvPolynomial (ThreeColumnCoefficientIndex n h) K
abbrev ThreeColumnCoefficientField (K n : Type*) [Field K] (h : ℕ) :=
  FractionRing (ThreeColumnCoefficientRing K n h)

def threeColumnUniversalFrame (K n : Type*) [Field K] (h : ℕ) :
    Matrix n (Fin 3) (ThreeColumnCoefficientRing K n h)[X] :=
  fun i j => ∑ k : Fin (h+1), monomial k.val (MvPolynomial.X (i,j,k))

theorem threeColumnUniversalFrame_coeff (K n : Type*) [Field K]
    (h : ℕ) (i : n) (j : Fin 3) (k : Fin (h+1)) :
    (threeColumnUniversalFrame K n h i j).coeff k.val=MvPolynomial.X (i,j,k) := by
  simp [threeColumnUniversalFrame,finset_sum_coeff,coeff_monomial,Fin.val_inj]

theorem threeColumnUniversalFrame_degree (K n : Type*) [Field K]
    (h : ℕ) (i : n) (j : Fin 3) :
    (threeColumnUniversalFrame K n h i j).natDegree≤h := by
  apply natDegree_sum_le_of_forall_le
  intro k _
  exact (natDegree_monomial_le _).trans (by have := k.isLt; omega)

theorem three_column_universal_pivot_ne_zero (K n : Type*) [Field K]
    (h : ℕ) (pivot : Fin 3 ↪ n) :
    (Matrix.of fun i j => (threeColumnUniversalFrame K n h (pivot i) j).coeff h).det≠0 := by
  classical
  let Q : Matrix (Fin 3) (Fin 3) (ThreeColumnCoefficientRing K n h) :=
    fun i j => (threeColumnUniversalFrame K n h (pivot i) j).coeff h
  let value : ThreeColumnCoefficientIndex n h → K := fun z => if z.1=pivot z.2.1 then 1 else 0
  have hc (i : n) (j : Fin 3) : (threeColumnUniversalFrame K n h i j).coeff h=
      MvPolynomial.X (i,j,Fin.last h) := threeColumnUniversalFrame_coeff K n h i j (Fin.last h)
  have hQ : Q.map (MvPolynomial.eval value)=1 := by
    ext i j
    simp only [Q,Matrix.map_apply,hc,
      MvPolynomial.eval_X,value,pivot.injective.eq_iff,Matrix.one_apply]
  have hdet : MvPolynomial.eval value Q.det=(Q.map (MvPolynomial.eval value)).det := by
    simpa only [RingHom.mapMatrix_apply] using (MvPolynomial.eval value).map_det Q
  rw [hQ,Matrix.det_one] at hdet
  intro hz
  change Q.det=0 at hz
  rw [hz,map_zero] at hdet
  exact zero_ne_one hdet

def threeColumnFractionFrame (K n : Type*) [Field K] (h : ℕ) :
    Matrix n (Fin 3) (ThreeColumnCoefficientField K n h)[X] :=
  (threeColumnUniversalFrame K n h).map (Polynomial.mapRingHom (algebraMap _ _))

theorem threeColumnFractionFrame_degree (K n : Type*) [Field K]
    (h : ℕ) (i : n) (j : Fin 3) :
    (threeColumnFractionFrame K n h i j).natDegree≤h :=
  natDegree_map_le.trans (threeColumnUniversalFrame_degree K n h i j)

theorem three_column_fraction_pivot_ne_zero (K n : Type*) [Field K]
    (h : ℕ) (pivot : Fin 3 ↪ n) :
    (Matrix.of fun i j => (threeColumnFractionFrame K n h (pivot i) j).coeff h).det≠0 := by
  let φ : ThreeColumnCoefficientRing K n h →+* ThreeColumnCoefficientField K n h := algebraMap _ _
  let Q : Matrix (Fin 3) (Fin 3) (ThreeColumnCoefficientRing K n h) :=
    fun i j => (threeColumnUniversalFrame K n h (pivot i) j).coeff h
  have he : (Matrix.of fun i j => (threeColumnFractionFrame K n h (pivot i) j).coeff h)=Q.map φ := by
    ext i j
    exact Polynomial.coeff_map φ h
  rw [he]
  have hdet : (Q.map φ).det=φ Q.det := by
    simpa only [RingHom.mapMatrix_apply] using (φ.map_det Q).symm
  rw [hdet]
  simpa only [map_zero] using (IsFractionRing.injective
    (ThreeColumnCoefficientRing K n h) (ThreeColumnCoefficientField K n h)).ne
      (three_column_universal_pivot_ne_zero K n h pivot)

end FD56
