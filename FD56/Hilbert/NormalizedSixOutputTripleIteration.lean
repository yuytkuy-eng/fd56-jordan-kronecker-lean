/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSixOutputTripleSplice
import Mathlib.FieldTheory.RatFunc.Basic

/-! Iterated normalized triple splices through a finite rational-function field tower. -/

noncomputable section
namespace FD56
open Matrix Polynomial
universe u
variable {K : Type u} [Field K] [CharZero K]

theorem normalized_six_output_triple_splice_iterate
    (G : Matrix (Fin 6) (Fin 3) K[X]) (a : ℕ)
    (hG : ∀ i j, (G i j).coeff 0=sixOutputTripleBaseFrame K i j)
    (hdG : ∀ i j, (G i j).natDegree≤a) (t : ℕ) :
    ∃ (L : Type u) (fieldL : Field L), letI := fieldL
      ∃ (_ : CharZero L) (_ : K →+* L) (G' : Matrix (Fin 6) (Fin 3) L[X]),
        (∀ i j, (G' i j).coeff 0=sixOutputTripleBaseFrame L i j) ∧
        (∀ i j, (G' i j).natDegree≤a+5*t) ∧
        ∀ d, Module.finrank L (polynomialKernelAtDegree
          (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G')) (d+6*t)) ≤
          Module.finrank K (polynomialKernelAtDegree
            (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)) d) := by
  induction t with
  | zero =>
    refine ⟨K,inferInstance,inferInstance,RingHom.id K,G,hG,?_,?_⟩
    · simpa using hdG
    · intro d
      simp
  | succ t ih =>
    obtain ⟨L,fieldL,charL,σ,H,hH,hdH,hdim⟩ := ih
    letI := fieldL
    letI := charL
    letI : CharZero (RatFunc L) :=
      charZero_of_injective_ringHom (algebraMap L (RatFunc L)).injective
    obtain ⟨H',hH',hdH',hdim'⟩ :=
      normalized_six_output_triple_splice_step (F:=RatFunc L) H (a+5*t) hH hdH
    refine ⟨RatFunc L,inferInstance,inferInstance,(algebraMap L (RatFunc L)).comp σ,
      H',hH',?_,?_⟩
    · intro i j
      simpa [Nat.mul_succ,Nat.add_assoc] using hdH' i j
    · intro d
      have h := (hdim' (d+6*t)).trans (hdim d)
      simpa [Nat.mul_succ,Nat.add_assoc] using h

end FD56
