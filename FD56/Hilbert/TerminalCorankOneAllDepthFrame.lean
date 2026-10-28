/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TerminalCorankOneScalarLifts
import FD56.Hilbert.ResidueOneAllDepthFrame

/-! Uniform SL kernel frames for state count mq+m-1 and m at least two. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable (s : ℕ)

def terminalOneFrameDegree (q : ℕ) : ℕ := ((s+2)*q^2+(3*s+4)*q+2*s)/2

theorem terminalOne_row_weight (q : ℕ) :
    (∑ k : Fin ((s+2)*q+s+1), (terminalOneLevel s q k+1))=
      terminalOneFrameDegree s q+1 := by
  have hs : 2*(∑ k : Fin ((s+2)*q+s+1), (terminalOneLevel s q k+1))=
      (s+2)*q^2+(3*s+4)*q+2*s+2 := by
    simp only [terminalOneLevel]
    rw [Nat.add_assoc,Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    have h (i : Fin (s+1)) : ((s+2)*q+i.val)/(s+2)=q := by
      rw [Nat.mul_add_div (by omega : 0<s+2),Nat.div_eq_of_lt (by omega : i.val<s+2),Nat.add_zero]
    simp_rw [h]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
    nlinarith [residueOne_prefix_row_weight (s+2) q]
  unfold terminalOneFrameDegree
  omega

variable {R : Type*} [CommRing R]

theorem terminalOne_shift_scalarU_zero (q : ℕ) :
    terminalOneScalarLiftMatrix s q (terminalOneShiftM (R:=R) s q)
      (terminalOneShiftP s q) (.inr (0,0)) 0=(q+1 : ℕ) := by
  have hsum : (∑ k : Fin ((s+2)*q+s+1), if k.val%(s+2)=0 then (1 : R) else 0)=
      ((q+1 : ℕ) : R) := by
    rw [Nat.add_assoc,Fin.sum_univ_add]
    simp only [Fin.coe_castAdd,Fin.coe_natAdd]
    rw [residueOne_prefix_zero_count (s+2) q]
    have h (i : Fin (s+1)) : ((s+2)*q+i.val)%(s+2)=0 ↔ i=0 := by
      have he : ((s+2)*q+i.val)%(s+2)=i.val := by
        simp [Nat.add_mod,Nat.mod_eq_of_lt (by omega : i.val<s+2)]
      rw [he]
      constructor
      · intro hi; exact Fin.ext (by simpa using hi)
      · intro hi; simp [hi]
    simp_rw [h]
    simp
  change observabilityScalarU (terminalOneShiftM (R:=R) s q)
    (observabilitySelectedMatrix (terminalOneShiftM s q) (terminalOneShiftP s q)
      (terminalOneLevel s q) (terminalOneRow s q 0)).adjugate
      (terminalOneLevel s q) (terminalOneRow s q 0) 0 0=_
  rw [terminalOne_shift_selected_zero,Matrix.adjugate_one]
  rw [← hsum]
  simp only [observabilityScalarU,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  have hk := Nat.mod_add_div k.val (s+2)
  simp [Matrix.mul_apply,observabilityScalarColumn,Matrix.one_apply,
    terminalOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,terminalOneLevel,terminalOneRow]
  split_ifs <;> simp_all <;> omega

variable {K : Type*} [Field K]

theorem terminalOne_scalar_lift_degree (q : ℕ)
    (M : Matrix (Fin ((s+2)*q+s+1)) (Fin ((s+2)*q+s+1)) K[X])
    (P : Matrix (Fin (s+2)) (Fin ((s+2)*q+s+1)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (terminalOneScalarLiftMatrix s q M P) (terminalOneFrameDegree s q) := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (terminalOneLevel s q) (terminalOneRow s q j) (terminalOneFrameDegree s q)
    (terminalOne_row_weight s q)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem terminalOne_shift_scalar_lift_injective [CharZero K] (q : ℕ) :
    Function.Injective (terminalOneScalarLiftMatrix s q
      (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q)).mulVec := by
  change Function.Injective (Matrix.toLin' (terminalOneScalarLiftMatrix s q
    (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change terminalOneScalarLiftMatrix s q (terminalOneShiftM (R:=K) s q)
    (terminalOneShiftP s q)*ᵥv=0 at hv
  have hentry (a : Fin (s+1)) (i : Fin ((s+2)*q+s+1)) (b : Fin (s+2)) :
      terminalOneScalarLiftMatrix s q (terminalOneShiftM (R:=K) s q)
        (terminalOneShiftP s q) (.inr (i,b)) a.succ=
        if i.val=a.val ∧ b=Fin.last (s+1) then 1 else 0 := terminalOne_shift_scalarU s q a i b
  have hlast : (0 : Fin (s+2))≠Fin.last (s+1) := by
    intro he
    have := congrArg Fin.val he
    simp at this
  have h0 := congrFun hv (.inr (0,0))
  change (∑ a : Fin (s+2), terminalOneScalarLiftMatrix s q
    (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q) (.inr (0,0)) a*v a)=0 at h0
  rw [Fin.sum_univ_succ] at h0
  have hz : (∑ a : Fin (s+1), terminalOneScalarLiftMatrix s q
      (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q) (.inr (0,0)) a.succ*v a.succ)=0 := by
    apply Finset.sum_eq_zero
    intro a _
    rw [hentry a 0 0]
    simp [hlast]
  rw [terminalOne_shift_scalarU_zero,hz,add_zero] at h0
  have hv0 : v 0=0 :=
    (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast (Nat.succ_ne_zero q))
  funext j
  refine Fin.cases (by exact hv0) (fun a => ?_) j
  let i : Fin ((s+2)*q+s+1) := ⟨a.val,by omega⟩
  have he := congrFun hv (.inr (i,Fin.last (s+1)))
  change (∑ b : Fin (s+2), terminalOneScalarLiftMatrix s q
    (terminalOneShiftM (R:=K) s q) (terminalOneShiftP s q) (.inr (i,Fin.last (s+1))) b*v b)=0 at he
  rw [Fin.sum_univ_succ,hv0,mul_zero,zero_add] at he
  rw [Finset.sum_eq_single a] at he
  · simpa [hentry,i] using he
  · intro b _ hb
    rw [hentry]
    have hne : i.val≠b.val := fun h => hb (Fin.ext h.symm)
    simp [hne]
  · simp

end FD56
