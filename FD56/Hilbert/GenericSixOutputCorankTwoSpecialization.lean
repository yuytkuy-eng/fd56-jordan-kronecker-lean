/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericCorankTwoPluckerSpecialization
import FD56.Hilbert.SixOutputCorankTwoGradients

/-! Faithful full Plucker coordinates for the actual six-output,
corank-two observability minors. Complementary signs are included. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {K : Type*} [Field K] [CharZero K]

private abbrev CorankTwoSixField (q : ℕ) :=
  AffineCoefficientField K (MatrixParameters (Fin (6*q+4)) (Fin 6))

theorem generic_six_output_corank_two_full_specialization_faithful (q : ℕ) (hq : 0<q) :
    ∃ (a b : ℕ) (u v : Fin 6 → (CorankTwoSixField (K:=K) q)[X]),
      (b=a ∨ b=a+1) ∧ a+b=interiorFullWeight 4 2 q ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      genericSixOutputCorankTwoMinors (K:=K) q=twoColumnWedge u v ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hrows,hfaithful⟩ :=
    generic_corank_two_plucker_specialization_faithful (K:=K) 4 q hq
  norm_num only [Nat.reduceAdd] at hsum
  have habsum : a+b=interiorFullWeight 4 2 q := by
    unfold interiorFullWeight
    norm_num only [Nat.reduceAdd,Nat.reduceMul]
    have he : 6*q*(q+1)+8*(q+1)=2*(a+b) := by nlinarith
    rw [he]
    omega
  refine ⟨a,b,u,v,hab,habsum,hu,hv,?_,hfaithful⟩
  have hminor (i : Fin 15) :
      sixOutputCorankTwoMinor q (genericAffineSquare K _ _) (genericAffineRows K _ _) i=
        twoColumnWedge u v (sixOutputPair i).1 (sixOutputPair i).2 := by
    have hi := hrows (sixOutputComplementaryRows i)
    simp only [sixOutputComplementaryRows_inl i,sixOutputComplementaryRows_inr i,
      corankTwoRowSign,sixOutputComplementaryRows_sign i,map_intCast,
      Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one] at hi
    unfold sixOutputCorankTwoMinor
    rw [hi]
    have hs : (sixOutputComplementarySign i : (CorankTwoSixField (K:=K) q)[X]) *
        (sixOutputComplementarySign i : (CorankTwoSixField (K:=K) q)[X])=1 := by
      rw [←Int.cast_mul,sixOutputComplementarySign_sq,Int.cast_one]
    rw [←mul_assoc,hs,one_mul]
    rfl
  change sixOutputAlternatingMatrix (sixOutputCorankTwoMinor q
    (genericAffineSquare K _ _) (genericAffineRows K _ _))=twoColumnWedge u v
  rw [funext hminor]
  exact sixOutputAlternatingMatrix_wedge u v

end FD56
