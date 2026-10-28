/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputOneScalarLifts

/-! A bounded rank-three SL kernel frame for every state count congruent to one modulo three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048

def threeOneFrameDegree (q : ℕ) : ℕ := (3*q^2+5*q)/2

theorem threeOne_row_weight (q : ℕ) :
    (∑ k : Fin (3*q+1), (threeOneLevel q k+1))=threeOneFrameDegree q+1 := by
  have haux (r : ℕ) : 2*(∑ k : Fin (3*r), (k.val/3+1))=3*r*(r+1) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have he : 3*(r+1)=3*r+1+1+1 := by omega
      rw [he,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc,Fin.val_last]
      have h₀ : 3*r/3=r := by omega
      have h₁ : (3*r+1)/3=r := by omega
      have h₂ : (3*r+1+1)/3=r := by omega
      rw [h₀,h₁,h₂]
      nlinarith
  have hs : 2*(∑ k : Fin (3*q+1), (threeOneLevel q k+1))=3*q^2+5*q+2 := by
    simp only [threeOneLevel,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last]
    have h₀ : 3*q/3=q := by omega
    rw [h₀]
    nlinarith [haux q]
  unfold threeOneFrameDegree
  omega

variable {R : Type*} [CommRing R]

theorem threeOne_shift_scalarU_zero (q : ℕ) :
    threeOneScalarLiftMatrix q (threeOneShiftM (R:=R) q) (threeOneShiftP q) (.inr (0,0)) 0=
      (q+1 : ℕ) := by
  have haux (r : ℕ) : (∑ k : Fin (3*r), if k.val%3=0 then (1 : R) else 0)=(r : R) := by
    induction r with
    | zero => simp
    | succ r ih =>
      have he : 3*(r+1)=3*r+1+1+1 := by omega
      rw [he,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
      simp only [Fin.coe_castSucc,Fin.val_last]
      rw [ih]
      have h₀ : 3*r%3=0 := by omega
      have h₁ : (3*r+1)%3=1 := by omega
      have h₂ : (3*r+1+1)%3=2 := by omega
      simp [h₀,h₁,h₂]
  have hsum : (∑ k : Fin (3*q+1), if k.val%3=0 then (1 : R) else 0)=((q+1 : ℕ) : R) := by
    rw [Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [haux]
    have h₀ : 3*q%3=0 := by omega
    simp [h₀]
  change observabilityScalarU (threeOneShiftM (R:=R) q)
    (observabilitySelectedMatrix (threeOneShiftM q) (threeOneShiftP q)
      (threeOneLevel q) (threeOneRow q 0)).adjugate
      (threeOneLevel q) (threeOneRow q 0) 0 0=_
  rw [threeOne_shift_selected_zero,Matrix.adjugate_one]
  rw [← hsum]
  simp only [observabilityScalarU,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply,observabilityScalarColumn,Matrix.one_apply,
    threeOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,threeOneLevel,threeOneRow]
  split_ifs <;> simp_all <;> omega

variable {K : Type*} [Field K]

theorem threeOne_scalar_lift_degree (q : ℕ)
    (M : Matrix (Fin (3*q+1)) (Fin (3*q+1)) K[X])
    (P : Matrix (Fin 3) (Fin (3*q+1)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (threeOneScalarLiftMatrix q M P) (threeOneFrameDegree q) := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (threeOneLevel q) (threeOneRow q j) (threeOneFrameDegree q) (threeOne_row_weight q)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem threeOne_shift_scalar_lift_injective [CharZero K] (q : ℕ) :
    Function.Injective (threeOneScalarLiftMatrix q
      (threeOneShiftM (R:=K) q) (threeOneShiftP q)).mulVec := by
  change Function.Injective (Matrix.toLin' (threeOneScalarLiftMatrix q
    (threeOneShiftM (R:=K) q) (threeOneShiftP q)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change threeOneScalarLiftMatrix q (threeOneShiftM (R:=K) q) (threeOneShiftP q)*ᵥv=0 at hv
  have hentry (a b : Fin 3) (ha : a≠0) :
      threeOneScalarLiftMatrix q (threeOneShiftM (R:=K) q) (threeOneShiftP q) (.inr (0,b)) a=
        if b=a then 1 else 0 := threeOne_shift_scalarU q a b ha
  have h0 := congrFun hv (.inr (0,0))
  have h1 := congrFun hv (.inr (0,1))
  have h2 := congrFun hv (.inr (0,2))
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h0
  change threeOneScalarLiftMatrix q (threeOneShiftM (R:=K) q) (threeOneShiftP q) (.inr (0,0)) 0*v 0+
    (threeOneScalarLiftMatrix q (threeOneShiftM (R:=K) q) (threeOneShiftP q) (.inr (0,0)) 1*v 1+
    threeOneScalarLiftMatrix q (threeOneShiftM (R:=K) q) (threeOneShiftP q) (.inr (0,0)) 2*v 2)=0 at h0
  rw [threeOne_shift_scalarU_zero,hentry 1 0 (by decide),hentry 2 0 (by decide)] at h0
  have hv0 : v 0=0 := by
    have h01 : (0 : Fin 3)≠1 := by decide
    have h02 : (0 : Fin 3)≠2 := by decide
    simp only [h01,h02,if_false,zero_mul,add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast (Nat.succ_ne_zero q))
  have hv1 : v 1=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,hentry] using h1
  have hv2 : v 2=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,hentry] using h2
  funext j
  fin_cases j <;> assumption


end FD56
