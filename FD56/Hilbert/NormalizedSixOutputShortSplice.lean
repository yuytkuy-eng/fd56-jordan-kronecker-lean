/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTangentSplice
import FD56.Hilbert.PermutedSixOutputThreeTailWitness
import FD56.Hilbert.SixOutputTangentPermutation

/-! A certified degree-three tail gives a normalized splice step over the
parameter fraction field, simultaneously for every bounded kernel degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

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
    (polynomialTailSplice u U 3).coeff 0=monomial 3 (U.coeff 0) := by
  simp [polynomialTailSplice,Finset.sum_range_succ,Polynomial.coeff_monomial]

variable {K F : Type*} [Field K] [CharZero K] [Field F]
  [Algebra K[X] F] [IsFractionRing K[X] F]

theorem normalized_six_output_short_splice_kernel_finrank_le
    (u v : Fin 6 → K[X])
    (hu : ∀ i, (u i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv : ∀ i, (v i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i) (d : ℕ) :
    Module.finrank F (polynomialKernelAtDegree
      ((sixOutputSpliceTangent u v permutedSixOutputThreeTailU permutedSixOutputThreeTailV 3).map
        (Polynomial.mapRingHom (algebraMap K[X] F))) (d+2)) ≤
      Module.finrank K (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u v)) d) := by
  apply six_output_tangent_splice_kernel_finrank_le
    u v permutedSixOutputThreeTailU permutedSixOutputThreeTailV 3 2 d (by omega)
    permutedSixOutputThreeTailU_degree permutedSixOutputThreeTailV_degree
  · intro i
    rw [permutedSixOutputThreeTailU_top,hu i]
  · intro i
    rw [permutedSixOutputThreeTailV_top,hv i]
  · exact permutedSixOutputThreeTail_bounded_kernel_zero_charZero

theorem normalized_six_output_short_splice_step
    (u v : Fin 6 → K[X]) (a b : ℕ)
    (hu : ∀ i, (u i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → K) i)
    (hv : ∀ i, (v i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → K) i)
    (hdu : ∀ i, (u i).natDegree≤a) (hdv : ∀ i, (v i).natDegree≤b) :
    ∃ u' v' : Fin 6 → F[X],
      (∀ i, (u' i).coeff 0=(![1,0,0,0,0,0] : Fin 6 → F) i) ∧
      (∀ i, (v' i).coeff 0=(![0,-1,0,0,0,0] : Fin 6 → F) i) ∧
      (∀ i, (u' i).natDegree≤a+3) ∧ (∀ i, (v' i).natDegree≤b+3) ∧
      ∀ d, Module.finrank F (polynomialKernelAtDegree
        (sixOutputPluckerTangent (twoColumnWedge u' v')) (d+2)) ≤
        Module.finrank K (polynomialKernelAtDegree
          (sixOutputPluckerTangent (twoColumnWedge u v)) d) := by
  let φ := algebraMap K[X] F
  let c := (φ ((X : K[X])^3))⁻¹
  let p : Fin 6 → F[X] := fun i => (polynomialTailSplice (u i) (permutedSixOutputThreeTailU i) 3).map φ
  let q : Fin 6 → F[X] := fun i => (polynomialTailSplice (v i) (permutedSixOutputThreeTailV i) 3).map φ
  let w : Fin 6 → F[X] := fun i => C c*p i
  let z : Fin 6 → F[X] := fun i => C c*q i
  let u' : Fin 6 → F[X] := w ∘ sixOutputTailSwap
  let v' : Fin 6 → F[X] := z ∘ sixOutputTailSwap
  have hx : φ ((X : K[X])^3)≠0 := by
    simpa only [map_zero] using
      (IsFractionRing.injective K[X] F).ne (pow_ne_zero 3 Polynomial.X_ne_zero)
  have hxp : (φ (X : K[X]))^3≠0 := by simpa only [map_pow] using hx
  have hc : c≠0 := inv_ne_zero hx
  have hconst (w W : K[X]) :
      (C c*(polynomialTailSplice w W 3).map φ).coeff 0=
        c*φ (monomial 3 (W.coeff 0)) := by
    rw [Polynomial.coeff_C_mul,Polynomial.coeff_map,splice_constant]
  refine ⟨u',v',?_,?_,?_,?_,?_⟩
  · intro i
    change (C c*(polynomialTailSplice (u (sixOutputTailSwap i)) (permutedSixOutputThreeTailU (sixOutputTailSwap i)) 3).map φ).coeff 0=_
    rw [hconst,permutedSixOutputThreeTailU_constant]
    fin_cases i <;> simp [sixOutputTailSwap,c,← Polynomial.C_mul_X_pow_eq_monomial,hxp]
  · intro i
    change (C c*(polynomialTailSplice (v (sixOutputTailSwap i)) (permutedSixOutputThreeTailV (sixOutputTailSwap i)) 3).map φ).coeff 0=_
    rw [hconst,permutedSixOutputThreeTailV_constant]
    fin_cases i <;> simp [sixOutputTailSwap,c,← Polynomial.C_mul_X_pow_eq_monomial,hxp]
  · intro i
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (polynomialTailSplice_degree _ _ 3 a (hdu (sixOutputTailSwap i))))
  · intro i
    exact (Polynomial.natDegree_C_mul_le _ _).trans
      (Polynomial.natDegree_map_le.trans (polynomialTailSplice_degree _ _ 3 b (hdv (sixOutputTailSwap i))))
  · intro d
    change Module.finrank F (polynomialKernelAtDegree
      (sixOutputPluckerTangent (twoColumnWedge (w ∘ sixOutputTailSwap) (z ∘ sixOutputTailSwap))) (d+2))≤_
    rw [six_output_tail_swap_kernel_finrank]
    have he : sixOutputPluckerTangent (twoColumnWedge w z)=
        (C c*C c) • ((sixOutputSpliceTangent u v permutedSixOutputThreeTailU permutedSixOutputThreeTailV 3).map
          (Polynomial.mapRingHom φ)) := by
      rw [tangent_scale]
      congr 1
      exact (tangent_map (Polynomial.mapRingHom φ) _ _).symm
    rw [he,kernel_smul _ _ (mul_ne_zero (Polynomial.C_ne_zero.mpr hc) (Polynomial.C_ne_zero.mpr hc))]
    exact normalized_six_output_short_splice_kernel_finrank_le u v hu hv d

end FD56
