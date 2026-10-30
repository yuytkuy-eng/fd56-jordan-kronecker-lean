/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialTailSplice
import FD56.LinearAlgebra.PolynomialTailKernelResidue
import FD56.LinearAlgebra.SixOutputPluckerTangent
import FD56.Hilbert.PolynomialKernelResidueDimension

/-! An explicit tail splice forces a degree shift in every specialized
tangent-kernel vector. The result retains the tail kernel test as a premise. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

private theorem tangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (u v : Fin 6 → R) :
    (sixOutputPluckerTangent (twoColumnWedge u v)).map φ=
      sixOutputPluckerTangent (twoColumnWedge (fun i => φ (u i)) (fun i => φ (v i))) := by
  rw [← sixOutputPluckerTangent_map]
  apply congrArg sixOutputPluckerTangent
  funext i j
  change φ (u i*v j-u j*v i)=φ (u i)*φ (v j)-φ (u j)*φ (v i)
  simp

private theorem tangent_scale {R : Type*} [CommRing R]
    (c : R) (u v : Fin 6 → R) :
    sixOutputPluckerTangent (twoColumnWedge (fun i => c*u i) (fun i => c*v i))=
      (c*c) • sixOutputPluckerTangent (twoColumnWedge u v) := by
  have he : twoColumnWedge (fun i => c*u i) (fun i => c*v i)=
      (c*c) • twoColumnWedge u v := by
    funext i j
    simp only [Matrix.smul_apply,twoColumnWedge,Pi.smul_apply,smul_eq_mul]
    ring
  rw [he,sixOutputPluckerTangent_smul]

variable {K : Type*} [Field K]

def sixOutputSpliceTangent (u v U V : Fin 6 → K[X]) (h : ℕ) :
    Matrix (Fin 15) (Fin 15) K[X][X] :=
  sixOutputPluckerTangent (twoColumnWedge
    (fun i => polynomialTailSplice (u i) (U i) h)
    (fun i => polynomialTailSplice (v i) (V i) h))

theorem six_output_tangent_splice_residue_shift
    (u v U V : Fin 6 → K[X]) (h k d : ℕ) (hk : 0<k)
    (hU : ∀ i, (U i).natDegree≤h) (hV : ∀ i, (V i).natDegree≤h)
    (hu : ∀ i, (U i).coeff h=(u i).coeff 0)
    (hv : ∀ i, (V i).coeff h=(v i).coeff 0)
    (hzero : ∀ z : Fin 15 → K[X],
      sixOutputPluckerTangent (twoColumnWedge U V)*ᵥz=0 →
      (∀ j, (z j).natDegree≤k-1) → z=0)
    (H : Fin 15 → K[X][X]) (hPH : sixOutputSpliceTangent u v U V h*ᵥH=0)
    (hdeg : ∀ j, (H j).natDegree≤d+k) :
    ∃ z : Fin 15 → K[X], sixOutputPluckerTangent (twoColumnWedge u v)*ᵥz=0 ∧
      (∀ j, (z j).natDegree≤d) ∧
      (fun j => (H j).map (Polynomial.evalRingHom 0))=(X : K[X])^k • z := by
  let Q := sixOutputPluckerTangent (twoColumnWedge
    (fun i => polynomialTailSpliceQuotient (u i) (U i) h)
    (fun i => polynomialTailSpliceQuotient (v i) (V i) h))
  have hQ : (fun i j => (Q i j).coeff 0)=sixOutputPluckerTangent (twoColumnWedge U V) := by
    change Q.map Polynomial.constantCoeff=_
    rw [tangent_map]
    have h₁ : (fun i => Polynomial.constantCoeff (polynomialTailSpliceQuotient (u i) (U i) h))=U := by
      funext i
      exact polynomialTailSpliceQuotient_constant _ _ _ (hU i) (hu i)
    have h₂ : (fun i => Polynomial.constantCoeff (polynomialTailSpliceQuotient (v i) (V i) h))=V := by
      funext i
      exact polynomialTailSpliceQuotient_constant _ _ _ (hV i) (hv i)
    rw [h₁,h₂]
  have hfactor : (sixOutputSpliceTangent u v U V h).map bivariateDiagonalRescaling=
      ((X : K[X][X])^h*X^h) • Q := by
    unfold sixOutputSpliceTangent
    rw [tangent_map]
    simp_rw [polynomialTailSplice_diagonal_factor]
    exact tangent_scale _ _ _
  have hQH : Q*ᵥ(fun j => bivariateDiagonalRescaling (H j))=0 := by
    have hm : ((sixOutputSpliceTangent u v U V h).map bivariateDiagonalRescaling)*ᵥ
        (fun j => bivariateDiagonalRescaling (H j))=0 := by
      funext i
      have he := congrArg bivariateDiagonalRescaling (congrFun hPH i)
      simpa [RingHom.map_mulVec,Function.comp_def] using he
    rw [hfactor,Matrix.smul_mulVec_assoc] at hm
    funext i
    have he := congrFun hm i
    change X^h*X^h*(Q*ᵥ(fun j => bivariateDiagonalRescaling (H j))) i=0 at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero
      (pow_ne_zero h Polynomial.X_ne_zero) (pow_ne_zero h Polynomial.X_ne_zero))
  have hdiv := polynomial_tail_kernel_residue_divisible Q H k hk hQH (by rw [hQ]; exact hzero)
  apply polynomial_kernel_shift_of_residue_divisible
    (sixOutputSpliceTangent u v U V h) (sixOutputPluckerTangent (twoColumnWedge u v))
    H (h+h) k d ?_ hPH hdiv hdeg
  unfold sixOutputSpliceTangent
  rw [tangent_map]
  change sixOutputPluckerTangent (twoColumnWedge
    (fun i => (polynomialTailSplice (u i) (U i) h).map (Polynomial.evalRingHom 0))
    (fun i => (polynomialTailSplice (v i) (V i) h).map (Polynomial.evalRingHom 0)))=_
  simp_rw [polynomialTailSplice_parameter_zero]
  rw [tangent_scale,pow_add]

theorem six_output_tangent_splice_kernel_finrank_le
    {F : Type*} [Field F] [Algebra K[X] F] [IsFractionRing K[X] F]
    (u v U V : Fin 6 → K[X]) (h k d : ℕ) (hk : 0<k)
    (hU : ∀ i, (U i).natDegree≤h) (hV : ∀ i, (V i).natDegree≤h)
    (hu : ∀ i, (U i).coeff h=(u i).coeff 0)
    (hv : ∀ i, (V i).coeff h=(v i).coeff 0)
    (hzero : ∀ z : Fin 15 → K[X],
      sixOutputPluckerTangent (twoColumnWedge U V)*ᵥz=0 →
      (∀ j, (z j).natDegree≤k-1) → z=0) :
    Module.finrank F (polynomialKernelAtDegree
      ((sixOutputSpliceTangent u v U V h).map
        (Polynomial.mapRingHom (algebraMap K[X] F))) (d+k)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u v)) d) := by
  apply polynomial_kernel_finrank_le_of_residue_divisible
    (sixOutputSpliceTangent u v U V h) (sixOutputPluckerTangent (twoColumnWedge u v))
    (h+h) k d
  · unfold sixOutputSpliceTangent
    rw [tangent_map]
    change sixOutputPluckerTangent (twoColumnWedge
      (fun i => (polynomialTailSplice (u i) (U i) h).map (Polynomial.evalRingHom 0))
      (fun i => (polynomialTailSplice (v i) (V i) h).map (Polynomial.evalRingHom 0)))=_
    simp_rw [polynomialTailSplice_parameter_zero]
    rw [tangent_scale,pow_add]
  · intro H hPH hdeg
    obtain ⟨z,_,_,hres⟩ := six_output_tangent_splice_residue_shift
      u v U V h k d hk hU hV hu hv hzero H hPH hdeg
    intro j
    exact ⟨z j,congrFun hres j⟩

end FD56
