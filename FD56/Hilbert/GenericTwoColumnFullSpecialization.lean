/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericTwoColumnPluckerSpecialization
import FD56.Hilbert.TwoColumnInteriorGradientBounds
import FD56.Hilbert.TwoColumnGradientAlternation
import FD56.LinearAlgebra.PluckerChartRecovery

/-! Faithful coefficient evaluation realizes every ordered two-row minor,
including coordinates outside the selected independent frame. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000

variable {K : Type*} [Field K] [CharZero K]
variable (s q : ℕ) [NeZero s]

private abbrev FullTwoColumnField :=
  AffineCoefficientField K (MatrixParameters (Fin ((2+s)*q+2)) (Fin (2+s)))

theorem generic_two_column_full_specialization_faithful (hq : 0<q) :
    ∃ (a b : ℕ) (u v : Fin (2+s) → (FullTwoColumnField (K:=K) s q)[X]),
      (b=a ∨ b=a+1) ∧ 2*(a+b)=(2+s)*q*(q+1)+4*(q+1) ∧
      (∀ i, (u i).natDegree≤a) ∧ (∀ i, (v i).natDegree≤b) ∧
      genericTwoColumnInteriorMinors (K:=K) s q=twoColumnWedge u v ∧
      Function.Injective (twoColumnMinorSpecialization a b
        (twoColumnCoefficientEvaluation (K:=K) a b u v)) := by
  obtain ⟨a,b,u,v,hab,hsum,hu,hv,hselected,hfaithful⟩ :=
    generic_two_column_plucker_specialization_faithful (K:=K) s q hq
  refine ⟨a,b,u,v,hab,hsum,hu,hv,?_,hfaithful⟩
  let F := genericTwoColumnInteriorMinors (K:=K) s q
  let G := twoColumnWedge u v
  have hcast0 : Fin.castAdd s (0:Fin 2)=(0:Fin (2+s)) := by
    apply Fin.ext; simp
  have hcast1 : Fin.castAdd s (1:Fin 2)=(1:Fin (2+s)) := by
    apply Fin.ext
    change 1=1%(2+s)
    rw [Nat.mod_eq_of_lt (by omega : 1<2+s)]
  have hsel (z : Option (Fin 2 × Fin s)) :
      F (interiorTerminalRow 2 s z 0) (interiorTerminalRow 2 s z 1)=
        G (interiorTerminalRow 2 s z 0) (interiorTerminalRow 2 s z 1) := by
    have h := hselected z
    change (observabilitySelectedMatrix _ _ (interiorLevel 2 s q)
      (twoColumnInteriorRow s q (interiorTerminalRow 2 s z 0,interiorTerminalRow 2 s z 1))).det=_
    rw [twoColumnInteriorRow_selected]
    exact h
  have h01 : F 0 1=G 0 1 := by
    have h := hsel none
    change F (Fin.castAdd s 0) (Fin.castAdd s 1)=G (Fin.castAdd s 0) (Fin.castAdd s 1) at h
    simpa only [hcast0,hcast1] using h
  obtain ⟨hFd,hFs⟩ := generic_two_column_minors_alternating (K:=K) s q
  change (∀ i, F i i=0) at hFd
  change (∀ i j, F j i= -F i j) at hFs
  have hGd (i : Fin (2+s)) : G i i=0 := by simp [G,twoColumnWedge]
  have hGs (i j : Fin (2+s)) : G j i= -G i j := by
    change u j*v i-u i*v j= -(u i*v j-u j*v i)
    ring
  have hfirst (j : Fin (2+s)) : F 0 j=G 0 j := by
    refine Fin.addCases (m:=2) (n:=s) ?_ ?_ j
    · intro i
      have hi : i=0 ∨ i=1 := by omega
      rcases hi with rfl|rfl
      · rw [hcast0,hFd,hGd]
      · rw [hcast1]; exact h01
    · intro i
      have h := hsel (some (1,i))
      simp only [interiorTerminalRow,show (0:Fin 2)≠1 by decide,if_false,if_true] at h
      change F (Fin.castAdd s 0) (Fin.natAdd 2 i)=G (Fin.castAdd s 0) (Fin.natAdd 2 i) at h
      simpa only [hcast0] using h
  have hsecond (j : Fin (2+s)) : F 1 j=G 1 j := by
    refine Fin.addCases (m:=2) (n:=s) ?_ ?_ j
    · intro i
      have hi : i=0 ∨ i=1 := by omega
      rcases hi with rfl|rfl
      · rw [hcast0,hFs 0 1,hGs 0 1,h01]
      · rw [hcast1,hFd,hGd]
    · intro i
      have h : F (Fin.natAdd 2 i) 1=G (Fin.natAdd 2 i) 1 := by
        have hh := hsel (some (0,i))
        simp only [interiorTerminalRow,show (1:Fin 2)≠0 by decide,if_false,if_true] at hh
        change F (Fin.natAdd 2 i) (Fin.castAdd s 1)=G (Fin.natAdd 2 i) (Fin.castAdd s 1) at hh
        simpa only [hcast1] using hh
      rw [hFs (Fin.natAdd 2 i) 1,hGs (Fin.natAdd 2 i) 1,h]
  have hbase : F 0 1≠0 := by
    rw [h01]
    exact two_column_faithful_base_minor_ne_zero a b u v hu hv hfaithful 0 1 (by simp; omega)
  apply plucker_matrix_eq_of_two_rows F G 0 1 hbase hfirst hsecond
  · exact fun i j => generic_two_column_minors_plucker_relation s q 0 1 i j
  · intro i j
    simpa only [one_smul] using scaled_wedge_plucker_relation (1 : (FullTwoColumnField (K:=K) s q)[X])
      u v 0 1 i j

end FD56
