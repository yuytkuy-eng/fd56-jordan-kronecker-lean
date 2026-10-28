/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerChartSystem

/-! Clearing the determinant of the chart reconstruction system produces
polynomial formulas that commute with coefficient specialization. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def pluckerChartRightHandSide {R : Type*} [CommRing R]
    (W : ℕ) (a b : R[X]) (c : R) : PluckerSystemInput W → R :=
  fun i => match pluckerSystemIndexEquiv W i with
    | Sum.inl k => (-(a*b)).coeff k.val
    | Sum.inr _ => c

def pluckerChartCramer {R : Type*} [CommRing R]
    (W : ℕ) (f g a b : R[X]) (c : R) : PluckerSystemInput W → R :=
  (pluckerChartSystem W f g).adjugate *ᵥ pluckerChartRightHandSide W a b c

def pluckerChartClearedVector {R : Type*} [CommRing R] [DecidableEq R]
    (W : ℕ) (F : Fin 4 → R[X]) (c : R) : Fin 6 → R[X] :=
  ![C (pluckerChartSystem W (F 0) (F 1)).det*F 0,
    C (pluckerChartSystem W (F 0) (F 1)).det*F 1,
    C (pluckerChartSystem W (F 0) (F 1)).det*F 2,
    C (pluckerChartSystem W (F 0) (F 1)).det*F 3,
    coefficientVectorPolynomial W (pluckerChartCramer W (F 0) (F 1) (F 2) (F 3) c) 0,
    coefficientVectorPolynomial W (pluckerChartCramer W (F 0) (F 1) (F 2) (F 3) c) 1]

theorem pluckerChartCramer_map {R S : Type*} [CommRing R] [CommRing S]
    (W : ℕ) (f g a b : R[X]) (c : R) (φ : R →+* S) :
    (fun i => φ (pluckerChartCramer W f g a b c i))=
      pluckerChartCramer W (f.map φ) (g.map φ) (a.map φ) (b.map φ) (φ c) := by
  have hrhs : (fun i => φ (pluckerChartRightHandSide W a b c i))=
      pluckerChartRightHandSide W (a.map φ) (b.map φ) (φ c) := by
    funext i
    dsimp only [pluckerChartRightHandSide]
    cases pluckerSystemIndexEquiv W i with
    | inl k => simp [← Polynomial.coeff_map]
    | inr k => rfl
  simp only [pluckerChartCramer,Matrix.mulVec,dotProduct,map_sum,map_mul]
  have hmatrix : (pluckerChartSystem W f g).adjugate.map φ=
      (pluckerChartSystem W (f.map φ) (g.map φ)).adjugate := by
    calc
      _ = ((pluckerChartSystem W f g).map φ).adjugate := φ.map_adjugate _
      _ = _ := by rw [pluckerChartSystem_map]
  funext i
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg₂ (·*·) (congrFun (congrFun hmatrix i) j) (congrFun hrhs j)

theorem pluckerChartClearedVector_map {R S : Type*} [CommRing R] [CommRing S]
    [DecidableEq R] [DecidableEq S]
    (W : ℕ) (F : Fin 4 → R[X]) (c : R) (φ : R →+* S) :
    (fun i => (pluckerChartClearedVector W F c i).map φ)=
      pluckerChartClearedVector W (fun i => (F i).map φ) (φ c) := by
  have hd : φ (pluckerChartSystem W (F 0) (F 1)).det=
      (pluckerChartSystem W ((F 0).map φ) ((F 1).map φ)).det := by
    calc
      _ = ((pluckerChartSystem W (F 0) (F 1)).map φ).det := φ.map_det _
      _ = _ := by rw [pluckerChartSystem_map]
  have hc := pluckerChartCramer_map W (F 0) (F 1) (F 2) (F 3) c φ
  funext i
  fin_cases i <;> simp [pluckerChartClearedVector,hd]
  all_goals
    simp only [coefficientVectorPolynomial,Polynomial.ofFn_eq_sum_monomial,
      Polynomial.map_sum,Polynomial.map_monomial]
    apply Finset.sum_congr rfl
    intro j _
    rw [congrFun hc _]

theorem pluckerChartCramer_solution {K : Type*} [Field K]
    (W : ℕ) (F : Fin 6 → K[X]) (hdegree : ∀ i,(F i).natDegree≤W)
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0) :
    pluckerChartCramer W (F 0) (F 1) (F 2) (F 3) ((F 4).coeff W)=
      fun j => (pluckerChartSystem W (F 0) (F 1)).det*
        (if j.1=0 then F 4 else F 5).coeff j.2.val := by
  classical
  let v : PluckerSystemInput W → K := fun j => (if j.1=0 then F 4 else F 5).coeff j.2.val
  have hv (j : Fin 2) : coefficientVectorPolynomial W v j=if j=0 then F 4 else F 5 := by
    change Polynomial.ofFn (W+1) (Polynomial.toFn (W+1) (if j=0 then F 4 else F 5))=_
    apply Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
    split_ifs <;> (have := hdegree (4 : Fin 6); have := hdegree (5 : Fin 6); omega)
  have hsol : pluckerChartSystem W (F 0) (F 1) *ᵥ v=
      pluckerChartRightHandSide W (F 2) (F 3) ((F 4).coeff W) := by
    funext i
    rw [pluckerChartSystem_mulVec,hv 0,hv 1]
    dsimp only [pluckerChartRightHandSide]
    cases pluckerSystemIndexEquiv W i with
    | inl k => simpa using congrArg (fun p : K[X] => p.coeff k.val) (eq_neg_of_add_eq_zero_left hquadric)
    | inr k => simp [v]
  dsimp only [pluckerChartCramer]
  rw [← hsol,Matrix.mulVec_mulVec,Matrix.adjugate_mul,Matrix.smul_mulVec_assoc,Matrix.one_mulVec]
  rfl

theorem pluckerChartClearedVector_eq {K : Type*} [Field K] [DecidableEq K]
    (W : ℕ) (F : Fin 6 → K[X]) (hdegree : ∀ i,(F i).natDegree≤W)
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0) :
    pluckerChartClearedVector W (fun i : Fin 4 => F (i.castAdd 2)) ((F 4).coeff W)=
      fun i => C (pluckerChartSystem W (F 0) (F 1)).det*F i := by
  have hc := pluckerChartCramer_solution W F hdegree hquadric
  have hpoly (j : Fin 2) : coefficientVectorPolynomial W
      (pluckerChartCramer W (F 0) (F 1) (F 2) (F 3) ((F 4).coeff W)) j=
      C (pluckerChartSystem W (F 0) (F 1)).det*(if j=0 then F 4 else F 5) := by
    rw [hc]
    change Polynomial.ofFn (W+1) (fun l =>
      (pluckerChartSystem W (F 0) (F 1)).det*(if j=0 then F 4 else F 5).coeff l.val)=_
    apply Polynomial.ext
    intro k
    by_cases hk : k<W+1
    · rw [Polynomial.ofFn_coeff_eq_val_of_lt _ hk,Polynomial.coeff_C_mul]
    · have hd : (if j=0 then F 4 else F 5).natDegree<k := by
        split_ifs <;> (have := hdegree (4 : Fin 6); have := hdegree (5 : Fin 6); omega)
      rw [Polynomial.ofFn_coeff_eq_zero_of_ge _ (by omega),Polynomial.coeff_C_mul,
        Polynomial.coeff_eq_zero_of_natDegree_lt hd,mul_zero]
  funext i
  fin_cases i <;> simp [pluckerChartClearedVector,hpoly]

end FD56
