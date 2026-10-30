/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.FiveOutputTangentSplice
import FD56.Hilbert.NormalizedSevenTailWitness

/-! A certified degree-seven tail gives a normalized splice step over the
parameter fraction field, simultaneously for every bounded kernel degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

private theorem tangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (u v : Fin 5 → R) :
    (fiveOutputPluckerTangent (twoColumnWedge u v)).map φ=
      fiveOutputPluckerTangent (twoColumnWedge (fun i => φ (u i)) (fun i => φ (v i))) := by
  funext i j
  fin_cases i <;> fin_cases j <;> simp [fiveOutputPluckerTangent,twoColumnWedge]

private theorem tangent_scale {R : Type*} [CommRing R]
    (c : R) (u v : Fin 5 → R) :
    fiveOutputPluckerTangent (twoColumnWedge (fun i => c*u i) (fun i => c*v i))=
      (c*c) • fiveOutputPluckerTangent (twoColumnWedge u v) := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [fiveOutputPluckerTangent,twoColumnWedge,Pi.smul_apply,smul_eq_mul] <;> ring

private theorem kernel_smul {F a b : Type*} [Field F] [Fintype b]
    (A : Matrix a b F[X]) (c : F[X]) (hc : c≠0) (d : ℕ) :
    polynomialKernelAtDegree (c • A) d=polynomialKernelAtDegree A d := by
  ext z
  change (c • A)*ᵥ(fun j => (z j).val)=0 ↔ A*ᵥ(fun j => (z j).val)=0
  rw [Matrix.smul_mulVec_assoc]
  constructor
  · intro h
    funext i
    exact (mul_eq_zero.mp (congrFun h i)).resolve_left hc
  · intro h
    rw [h,smul_zero]

private theorem splice_constant {K : Type*} [Field K] (u U : K[X]) :
    (polynomialTailSplice u U 7).coeff 0=monomial 7 (U.coeff 0) := by
  simp [polynomialTailSplice,Finset.sum_range_succ,Polynomial.coeff_monomial]

variable {K F : Type*} [Field K] [CharZero K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]

theorem normalized_five_output_splice_kernel_finrank_le
    (u v : Fin 5 → K[X])
    (hu : ∀ i, (u i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv : ∀ i, (v i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i) (d : ℕ) :
    Module.finrank F (polynomialKernelAtDegree
      ((fiveOutputSpliceTangent u v normalizedSevenTailU normalizedSevenTailV 7).map
        (Polynomial.mapRingHom (algebraMap K[X] F))) (d+4)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u v)) d) := by
  apply five_output_tangent_splice_kernel_finrank_le
    u v normalizedSevenTailU normalizedSevenTailV 7 4 d (by omega)
    normalizedSevenTailU_degree normalizedSevenTailV_degree
  · intro i
    rw [normalizedSevenTailU_top,hu i]
  · intro i
    rw [normalizedSevenTailV_top,hv i]
  · exact normalizedSevenTail_bounded_kernel_zero_charZero

theorem normalized_five_output_splice_step
    (u v : Fin 5 → K[X]) (a b : ℕ)
    (hu : ∀ i, (u i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv : ∀ i, (v i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu : ∀ i, (u i).natDegree≤a) (hdv : ∀ i, (v i).natDegree≤b) :
    ∃ u' v' : Fin 5 → F[X],
      (∀ i, (u' i).coeff 0=(![1,0,0,0,0] : Fin 5 → F) i) ∧
      (∀ i, (v' i).coeff 0=(![0,-1,0,0,0] : Fin 5 → F) i) ∧
      (∀ i, (u' i).natDegree≤a+7) ∧ (∀ i, (v' i).natDegree≤b+7) ∧
      ∀ d, Module.finrank F (polynomialKernelAtDegree
        (fiveOutputPluckerTangent (twoColumnWedge u' v')) (d+4)) ≤
        Module.finrank K (polynomialKernelAtDegree
          (fiveOutputPluckerTangent (twoColumnWedge u v)) d) := by
  let φ := algebraMap K[X] F
  let c := (φ ((X : K[X])^7))⁻¹
  let p : Fin 5 → F[X] := fun i => (polynomialTailSplice (u i) (normalizedSevenTailU i) 7).map φ
  let q : Fin 5 → F[X] := fun i => (polynomialTailSplice (v i) (normalizedSevenTailV i) 7).map φ
  let u' : Fin 5 → F[X] := fun i => C c*p i
  let v' : Fin 5 → F[X] := fun i => C c*q i
  have hx : φ ((X : K[X])^7)≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] F).ne (pow_ne_zero 7 Polynomial.X_ne_zero)
  have hxp : (φ (X : K[X]))^7≠0 := by simpa only [map_pow] using hx
  have hc : c≠0 := inv_ne_zero hx
  have hconst (w W : K[X]) :
      (C c*(polynomialTailSplice w W 7).map φ).coeff 0=
        c*φ (monomial 7 (W.coeff 0)) := by
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,splice_constant]
  refine ⟨u',v',?_,?_,?_,?_,?_⟩
  · intro i
    change (C c*(polynomialTailSplice (u i) (normalizedSevenTailU i) 7).map φ).coeff 0=_
    rw [hconst,normalizedSevenTailU_constant]
    fin_cases i <;> simp [c,← Polynomial.C_mul_X_pow_eq_monomial,hxp]
  · intro i
    change (C c*(polynomialTailSplice (v i) (normalizedSevenTailV i) 7).map φ).coeff 0=_
    rw [hconst,normalizedSevenTailV_constant]
    fin_cases i <;> simp [c,← Polynomial.C_mul_X_pow_eq_monomial,hxp]
  · intro i
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (polynomialTailSplice_degree _ _ 7 a (hdu i)))
  · intro i
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (polynomialTailSplice_degree _ _ 7 b (hdv i)))
  · intro d
    have he : fiveOutputPluckerTangent (twoColumnWedge u' v')=
        (C c*C c) • ((fiveOutputSpliceTangent u v normalizedSevenTailU normalizedSevenTailV 7).map
          (Polynomial.mapRingHom φ)) := by
      rw [tangent_scale]
      congr 1
      exact (tangent_map (Polynomial.mapRingHom φ) _ _).symm
    rw [he,kernel_smul _ _ (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) (Polynomial.C_ne_zero.mpr hc))]
    exact normalized_five_output_splice_kernel_finrank_le u v hu hv d

end FD56
