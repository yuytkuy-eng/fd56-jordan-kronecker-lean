/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericCorankTwoPluckerSpecialization
import FD56.Hilbert.FiveOutputCorankTwoGradients

/-! Faithful full Plucker coordinates for the actual five-output,
corank-two observability minors. Complementary signs are included. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private abbrev CorankTwoFiveField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (5*q+3)) (Fin 5))

theorem generic_five_output_corank_two_full_specialization_faithful (q : ℕ) (hq : 0<q) :
    ∃ (a b : ℕ) (u v : Fin 5 → (CorankTwoFiveField (K:=K) q)[X]),
      (b=a ∨ b=a+1) ∧ a+b=interiorFullWeight 3 2 q ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      genericFiveOutputCorankTwoMinors (K:=K) q=twoColumnWedge u v ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hrows,hfaithful⟩ :=
    generic_corank_two_plucker_specialization_faithful (K:=K) 3 q hq
  norm_num only [Nat.reduceAdd] at hsum
  have habsum : a+b=interiorFullWeight 3 2 q := by
    unfold interiorFullWeight
    norm_num only [Nat.reduceAdd,Nat.reduceMul]
    have he : 5*q*(q+1)+6*(q+1)=2*(a+b) := by nlinarith
    rw [he]
    omega
  refine ⟨a,b,u,v,hab,habsum,hu,hv,?_,hfaithful⟩
  have hminor (i : Fin 10) :
      fiveOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _) i=
        twoColumnWedge u v (fiveOutputPair i).1 (fiveOutputPair i).2 := by
    have hi := hrows (fiveOutputComplementaryRows i)
    simp only [fiveOutputComplementaryRows_inl i,fiveOutputComplementaryRows_inr i,
      corankTwoRowSign,fiveOutputComplementaryRows_sign i,map_intCast,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hi
    unfold fiveOutputCorankTwoMinor
    rw [hi]
    have hs : (fiveOutputComplementarySign i : (CorankTwoFiveField (K:=K) q)[X]) *
        (fiveOutputComplementarySign i : (CorankTwoFiveField (K:=K) q)[X])=1 := by
      rw [←Int.cast_mul,fiveOutputComplementarySign_sq,Int.cast_one]
    rw [←mul_assoc,hs,one_mul]
    rfl
  change fiveOutputAlternatingMatrix (fiveOutputCorankTwoMinor q
    (genericAffineSquare K _ _) (genericAffineRows K _ _))=twoColumnWedge u v
  rw [funext hminor]
  exact fiveOutputAlternatingMatrix_wedge u v

end FD56
