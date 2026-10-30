/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedFiveOutputSplice
import Mathlib.FieldTheory.RatFunc.Basic

/-! Iterating the normalized splice through successive rational-function
fields. The resulting extension retains all bounded-kernel inequalities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem normalized_five_output_splice_iterate
    (u v : Fin 5 → K[X]) (a b : ℕ)
    (hu : ∀ i, (u i).coeff 0=(![1,0,0,0,0] : Fin 5 → K) i)
    (hv : ∀ i, (v i).coeff 0=(![0,-1,0,0,0] : Fin 5 → K) i)
    (hdu : ∀ i, (u i).natDegree≤a) (hdv : ∀ i, (v i).natDegree≤b) (t : ℕ) :
    ∃ (L : Type u) (fieldL : Field L), letI := fieldL
      ∃ (_ : CharZero L) (_ : K →+* L) (u' v' : Fin 5 → L[X]),
        (∀ i, (u' i).coeff 0=(![1,0,0,0,0] : Fin 5 → L) i) ∧
        (∀ i, (v' i).coeff 0=(![0,-1,0,0,0] : Fin 5 → L) i) ∧
        (∀ i, (u' i).natDegree≤a+7*t) ∧ (∀ i, (v' i).natDegree≤b+7*t) ∧
        ∀ d, Module.finrank L (polynomialKernelAtDegree
          (fiveOutputPluckerTangent (twoColumnWedge u' v')) (d+4*t)) ≤
          Module.finrank K (polynomialKernelAtDegree
            (fiveOutputPluckerTangent (twoColumnWedge u v)) d) := by
  induction t with
  | zero =>
    refine ⟨K,inferInstance,inferInstance,RingHom.id K,u,v,hu,hv,?_,?_,?_⟩
    · simpa using hdu
    · simpa using hdv
    · intro d
      simp
  | succ t ih =>
    obtain ⟨L,fieldL,charL,σ,w,z,hw,hz,hdw,hdz,hdim⟩ := ih
    letI := fieldL
    letI := charL
    letI : CharZero (RatFunc L) :=
      charZero_of_injective_ringHom (algebraMap L (RatFunc L)).injective
    obtain ⟨w',z',hw',hz',hdw',hdz',hdim'⟩ :=
      normalized_five_output_splice_step (F:=RatFunc L) w z (a+7*t) (b+7*t)
        hw hz hdw hdz
    refine ⟨RatFunc L,inferInstance,inferInstance,(algebraMap L (RatFunc L)).comp σ,
      w',z',hw',hz',?_,?_,?_⟩
    · intro i
      simpa [Nat.mul_succ,Nat.add_assoc] using hdw' i
    · intro i
      simpa [Nat.mul_succ,Nat.add_assoc] using hdz' i
    · intro d
      have h := (hdim' (d+4*t)).trans (hdim d)
      simpa [Nat.mul_succ,Nat.add_assoc] using h

end FD56
