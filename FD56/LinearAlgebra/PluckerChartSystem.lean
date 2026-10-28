/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerChartReconstruction
import FD56.LinearAlgebra.CoefficientMatrix

/-! A coefficient-ring linear system for the coprime Plucker chart. Its
coefficients commute with specialization and its determinant is nonzero
on the full-degree coprime chart. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

abbrev PluckerSystemInput (W : ℕ) := Fin 2 × Fin (W+1)
abbrev PluckerSystemOutput (W : ℕ) := Fin (2*W+1) ⊕ Unit

def pluckerSystemIndexEquiv (W : ℕ) : PluckerSystemInput W ≃ PluckerSystemOutput W :=
  Fintype.equivOfCardEq (by simp [PluckerSystemInput,PluckerSystemOutput]; omega)

def pluckerChartCoefficientSystem {R : Type*} [CommRing R]
    (W : ℕ) (f g : R[X]) : Matrix (PluckerSystemOutput W) (PluckerSystemInput W) R :=
  fun i j => match i with
    | Sum.inl k => ((if j.1=0 then -g else f)*X^j.2.val).coeff k.val
    | Sum.inr _ => if j=(0,⟨W,Nat.lt_succ_self W⟩) then 1 else 0

def pluckerChartSystem {R : Type*} [CommRing R]
    (W : ℕ) (f g : R[X]) : Matrix (PluckerSystemInput W) (PluckerSystemInput W) R :=
  (pluckerChartCoefficientSystem W f g).submatrix (pluckerSystemIndexEquiv W) id

theorem pluckerChartSystem_map {R S : Type*} [CommRing R] [CommRing S]
    (W : ℕ) (f g : R[X]) (φ : R →+* S) :
    (pluckerChartSystem W f g).map φ=pluckerChartSystem W (f.map φ) (g.map φ) := by
  funext i j
  change φ (pluckerChartCoefficientSystem W f g (pluckerSystemIndexEquiv W i) j)=_
  cases h : pluckerSystemIndexEquiv W i with
  | inl k =>
    simp only [pluckerChartSystem,Matrix.submatrix,h,pluckerChartCoefficientSystem,id_eq]
    rw [← Polynomial.coeff_map]
    simp only [Polynomial.map_mul,Polynomial.map_pow,Polynomial.map_X]
    split_ifs <;> simp_all
  | inr k =>
    simp [pluckerChartSystem,Matrix.submatrix,h,pluckerChartCoefficientSystem]

private theorem pluckerChartCoefficientSystem_mulVec
    {R : Type*} [CommRing R] [DecidableEq R] (W : ℕ) (f g : R[X])
    (v : PluckerSystemInput W → R) (k : Fin (2*W+1)) :
    (pluckerChartCoefficientSystem W f g *ᵥ v) (Sum.inl k)=
      (f*coefficientVectorPolynomial W v 1-g*coefficientVectorPolynomial W v 0).coeff k.val := by
  have h (j : Fin 2) (l : Fin (W+1)) :
      (((if j=0 then -g else f)*X^l.val).coeff k.val)*v (j,l)=
      ((if j=0 then -g else f)*Polynomial.monomial l.val (v (j,l))).coeff k.val := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    rw [show (if j=0 then -g else f)*(C (v (j,l))*X^l.val)=
      C (v (j,l))*((if j=0 then -g else f)*X^l.val) by ring,Polynomial.coeff_C_mul]
    ring
  simp only [Matrix.mulVec,dotProduct,pluckerChartCoefficientSystem,Fintype.sum_prod_type,h]
  simp [coefficientVectorPolynomial,Polynomial.ofFn_eq_sum_monomial,
    Fin.sum_univ_two,Finset.mul_sum,Polynomial.finset_sum_coeff,sub_eq_add_neg,add_comm]

theorem pluckerChartSystem_mulVec {R : Type*} [CommRing R] [DecidableEq R]
    (W : ℕ) (f g : R[X]) (v : PluckerSystemInput W → R) (i : PluckerSystemInput W) :
    (pluckerChartSystem W f g *ᵥ v) i =
      match pluckerSystemIndexEquiv W i with
      | Sum.inl k => (f*coefficientVectorPolynomial W v 1-
          g*coefficientVectorPolynomial W v 0).coeff k.val
      | Sum.inr _ => v (0,⟨W,Nat.lt_succ_self W⟩) := by
  change (pluckerChartCoefficientSystem W f g *ᵥ v) (pluckerSystemIndexEquiv W i)=_
  cases pluckerSystemIndexEquiv W i with
  | inl k => exact pluckerChartCoefficientSystem_mulVec W f g v k
  | inr k => simp [Matrix.mulVec,dotProduct,pluckerChartCoefficientSystem]

theorem pluckerChartSystem_injective {K : Type*} [Field K]
    (W : ℕ) (f g : K[X]) (hf : f.natDegree≤W) (hg : g.natDegree≤W)
    (hf0 : f≠0) (hdegree : f.natDegree=W) (hcoprime : IsCoprime f g) :
    Function.Injective (pluckerChartSystem W f g).mulVec := by
  classical
  change Function.Injective (Matrix.toLin' (pluckerChartSystem W f g))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change pluckerChartSystem W f g *ᵥ v=0 at hv
  have hv' : pluckerChartCoefficientSystem W f g *ᵥ v=0 := by
    funext i
    obtain ⟨j,rfl⟩ := (pluckerSystemIndexEquiv W).surjective i
    exact congrFun hv j
  let p : BoundedPoly K W := boundedPolyOf (coefficientVectorPolynomial W v 0)
    (coefficientVectorPolynomial_degree W v 0)
  let q : BoundedPoly K W := boundedPolyOf (coefficientVectorPolynomial W v 1)
    (coefficientVectorPolynomial_degree W v 1)
  have hrel : f*q.val-g*p.val=0 := by
    apply Polynomial.ext
    intro k
    by_cases hk : k<2*W+1
    · have h := congrFun hv' (Sum.inl ⟨k,hk⟩)
      rw [pluckerChartCoefficientSystem_mulVec] at h
      exact h
    · have hd : (f*q.val-g*p.val).natDegree≤2*W := by
        apply (Polynomial.natDegree_sub_le _ _).trans
        apply max_le
        · exact Polynomial.natDegree_mul_le.trans (by have := boundedPoly_degree W q; omega)
        · exact Polynomial.natDegree_mul_le.trans (by have := boundedPoly_degree W p; omega)
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega),Polynomial.coeff_zero]
  have hcoeff : p.val.coeff W=0 := by
    have h := congrFun hv' (Sum.inr ())
    simpa [p,boundedPolyOf,coefficientVectorPolynomial,Polynomial.ofFn_coeff_eq_val_of_lt,
      Matrix.mulVec,dotProduct,pluckerChartCoefficientSystem] using h
  have hpq : (p,q)=(0,0) := by
    apply pluckerChartReconstructionMap_injective W f g hf hg hf0 hdegree hcoprime
    change _=pluckerChartReconstructionMap W f g hf hg (0 : BoundedPoly K W × BoundedPoly K W)
    rw [map_zero]
    exact Prod.ext (Subtype.ext hrel) hcoeff
  have hz (j : Fin 2) : coefficientVectorPolynomial W v j=0 := by
    fin_cases j
    · exact congrArg (fun z : BoundedPoly K W × BoundedPoly K W => z.1.val) hpq
    · exact congrArg (fun z : BoundedPoly K W × BoundedPoly K W => z.2.val) hpq
  funext j
  have h := congrArg (fun p : K[X] => p.coeff j.2.val) (hz j.1)
  simpa [coefficientVectorPolynomial,Polynomial.ofFn_coeff_eq_val_of_lt] using h

theorem pluckerChartSystem_det_ne_zero {K : Type*} [Field K]
    (W : ℕ) (f g : K[X]) (hf : f.natDegree≤W) (hg : g.natDegree≤W)
    (hf0 : f≠0) (hdegree : f.natDegree=W) (hcoprime : IsCoprime f g) :
    (pluckerChartSystem W f g).det≠0 := by
  obtain ⟨L,hL⟩ := matrix_left_inverse_of_injective (pluckerChartSystem W f g)
    (pluckerChartSystem_injective W f g hf hg hf0 hdegree hcoprime)
  have h := congrArg Matrix.det hL
  rw [Matrix.det_mul,Matrix.det_one] at h
  intro hz
  rw [hz,mul_zero] at h
  exact zero_ne_one h

end FD56
