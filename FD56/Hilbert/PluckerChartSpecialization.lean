/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerChartCramer
import FD56.LinearAlgebra.PluckerChartDerivationCoordinates
import FD56.Hilbert.GenericPrescribedMatrix

/-! Algebraically independent coprime chart coordinates transfer every
bounded-kernel rank certificate from another point of the same chart. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def universalPluckerChartFirst (K : Type*) [Field K] (W : ℕ) :
    Fin 4 → (MvPolynomial (PluckerChartIndex W) K)[X] := by
  classical
  exact fun i => Polynomial.ofFn (W+1) (fun j => MvPolynomial.X (Sum.inl (i,j)))

def universalPluckerChartCleared (K : Type*) [Field K] (W : ℕ) :
    Fin 6 → (MvPolynomial (PluckerChartIndex W) K)[X] := by
  classical
  exact pluckerChartClearedVector W (universalPluckerChartFirst K W) (MvPolynomial.X (Sum.inr ()))

def pluckerChartSpecialization {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ℕ) (F : Fin 6 → L[X]) : MvPolynomial (PluckerChartIndex W) K →+* L :=
  MvPolynomial.eval₂Hom (algebraMap K L) (pluckerChartCoordinates W F)

theorem universalPluckerChartFirst_specialization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ℕ) (F : Fin 6 → L[X]) (hF : ∀ i,(F i).natDegree≤W) :
    (fun i => (universalPluckerChartFirst K W i).map (pluckerChartSpecialization (K:=K) W F))=
      fun i : Fin 4 => F (i.castAdd 2) := by
  classical
  funext i
  change (Polynomial.ofFn (W+1) _).map _=_
  calc
    _ = Polynomial.ofFn (W+1) (fun j => (F (i.castAdd 2)).coeff j.val) := by
      simp only [Polynomial.ofFn_eq_sum_monomial,Polynomial.map_sum,Polynomial.map_monomial,
        pluckerChartSpecialization,MvPolynomial.eval₂Hom_X']
      rfl
    _ = _ := Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt (by have := hF (i.castAdd 2); omega)

theorem universalPluckerChartCleared_specialization
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ℕ) (F : Fin 6 → L[X]) (hF : ∀ i,(F i).natDegree≤W)
    (hquadric : F 0*F 5-F 1*F 4+F 2*F 3=0) :
    (fun i => (universalPluckerChartCleared K W i).map (pluckerChartSpecialization (K:=K) W F))=
      fun i => C (pluckerChartSystem W (F 0) (F 1)).det*F i := by
  classical
  change (fun i => (pluckerChartClearedVector W _ _ i).map _)=_
  rw [pluckerChartClearedVector_map,universalPluckerChartFirst_specialization W F hF]
  simp only [pluckerChartSpecialization,MvPolynomial.eval₂Hom_X']
  change pluckerChartClearedVector W (fun i : Fin 4 => F (i.castAdd 2)) ((F 4).coeff W)=_
  exact pluckerChartClearedVector_eq W F hF hquadric

private theorem row_kernel_nonzero_scalar {K : Type*} [Field K]
    (F : Fin 6 → K[X]) (c : K) (hc : c≠0) (d : ℕ) :
    polynomialKernelAtDegree (fun _ : Unit => fun i => C c*F i) d=
      polynomialKernelAtDegree (fun _ : Unit => F) d := by
  ext v
  change ((fun _ : Unit => fun i => C c*F i) *ᵥ (fun j => (v j).val)=0) ↔
    ((fun _ : Unit => F) *ᵥ (fun j => (v j).val)=0)
  have hC : (C c : K[X])≠0 := by simpa using hc
  simp only [funext_iff,Matrix.mulVec,dotProduct,mul_assoc,← Finset.mul_sum]
  simp [hC]

theorem pluckerChart_kernel_le_witness
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (W : ℕ) (F : Fin 6 → L[X]) (G : Fin 6 → K[X])
    (hF : ∀ i,(F i).natDegree≤W) (hG : ∀ i,(G i).natDegree≤W)
    (hF0 : F 0≠0) (hFd : (F 0).natDegree=W) (hFc : IsCoprime (F 0) (F 1))
    (hG0 : G 0≠0) (hGd : (G 0).natDegree=W) (hGc : IsCoprime (G 0) (G 1))
    (hFq : F 0*F 5-F 1*F 4+F 2*F 3=0)
    (hGq : G 0*G 5-G 1*G 4+G 2*G 3=0)
    (hind : AlgebraicIndependent K (pluckerChartCoordinates W F)) (d : ℕ) :
    Module.finrank L (polynomialKernelAtDegree (fun _ : Unit => F) d)≤
      Module.finrank K (polynomialKernelAtDegree (fun _ : Unit => G) d) := by
  classical
  let φ := pluckerChartSpecialization (K:=K) W F
  let ψ := pluckerChartSpecialization (K:=K) W G
  let A : Matrix Unit (Fin 6) (MvPolynomial (PluckerChartIndex W) K)[X] :=
    fun _ => universalPluckerChartCleared K W
  let cF := (pluckerChartSystem W (F 0) (F 1)).det
  let cG := (pluckerChartSystem W (G 0) (G 1)).det
  have hcF : cF≠0 := pluckerChartSystem_det_ne_zero W _ _ (hF 0) (hF 1) hF0 hFd hFc
  have hcG : cG≠0 := pluckerChartSystem_det_ne_zero W _ _ (hG 0) (hG 1) hG0 hGd hGc
  have hφ : Function.Injective φ := hind
  have heF : A.map (Polynomial.mapRingHom φ)=(fun _ : Unit => fun i => C cF*F i) := by
    funext i j
    exact congrFun (universalPluckerChartCleared_specialization W F hF hFq) j
  have heG : A.map (Polynomial.mapRingHom ψ)=(fun _ : Unit => fun i => C cG*G i) := by
    funext i j
    exact congrFun (universalPluckerChartCleared_specialization W G hG hGq) j
  have hr := matrix_kernel_finrank_le_of_field_specialization ψ φ hφ
    (weightedCoefficientMatrix A (fun _ => d) (fun _ => d+W))
  rw [← weightedCoefficientMatrix_map,← weightedCoefficientMatrix_map,heF,heG] at hr
  rw [weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have h := Polynomial.natDegree_mul_le (p:=C cF) (q:=F j)
    have := hF j
    simp only [Polynomial.natDegree_C,zero_add] at h
    omega),weighted_coefficient_kernel_finrank _ _ _ (by
    intro i j
    have h := Polynomial.natDegree_mul_le (p:=C cG) (q:=G j)
    have := hG j
    simp only [Polynomial.natDegree_C,zero_add] at h
    omega)] at hr
  change Module.finrank L (polynomialKernelAtDegree (fun _ : Unit => fun i => C cF*F i) d)≤
    Module.finrank K (polynomialKernelAtDegree (fun _ : Unit => fun i => C cG*G i) d) at hr
  rwa [row_kernel_nonzero_scalar F cF hcF d,row_kernel_nonzero_scalar G cG hcG d] at hr

end FD56
