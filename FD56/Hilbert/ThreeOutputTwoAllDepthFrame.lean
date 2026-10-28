/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputTwoScalarLifts

/-! A bounded rank-three SL kernel frame for every state count congruent to two modulo three. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

def threeTwoFrameDegree (q : ℕ) : ℕ := (3*q^2+7*q+2)/2

theorem threeTwo_row_weight (q : ℕ) :
    (∑ k : Fin (3*q+2), (threeTwoLevel q k+1))=threeTwoFrameDegree q+1 := by
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
  have hs : 2*(∑ k : Fin (3*q+2), (threeTwoLevel q k+1))=3*q^2+7*q+4 := by
    simp only [threeTwoLevel,Fin.sum_univ_castSucc,Fin.coe_castSucc,Fin.val_last]
    have h₀ : 3*q/3=q := by omega
    have h₁ : (3*q+1)/3=q := by omega
    rw [h₀,h₁]
    nlinarith [haux q]
  unfold threeTwoFrameDegree
  omega

variable {R : Type*} [CommRing R]

theorem threeTwo_shift_scalarU_zero (q : ℕ) :
    threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=R) q) (threeTwoShiftP q) (.inr (0,0)) 0=
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
  have hsum : (∑ k : Fin (3*q+2), if k.val%3=0 then (1 : R) else 0)=((q+1 : ℕ) : R) := by
    rw [Fin.sum_univ_castSucc,Fin.sum_univ_castSucc]
    simp only [Fin.coe_castSucc,Fin.val_last]
    rw [haux]
    have h₀ : 3*q%3=0 := by omega
    have h₁ : (3*q+1)%3=1 := by omega
    simp [h₀,h₁]
  change observabilityScalarU (threeTwoShiftM (R:=R) q)
    (observabilitySelectedMatrix (threeTwoShiftM q) (threeTwoShiftP q)
      (threeTwoLevel q) (threeTwoRow q 0)).adjugate
      (threeTwoLevel q) (threeTwoRow q 0) 0 0=_
  rw [threeTwo_shift_selected_zero,Matrix.adjugate_one]
  rw [← hsum]
  simp only [observabilityScalarU,Matrix.sum_apply]
  apply Finset.sum_congr rfl
  intro k _
  simp [Matrix.mul_apply,observabilityScalarColumn,Matrix.one_apply,
    threeTwoShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,threeTwoLevel,threeTwoRow]
  split_ifs <;> simp_all <;> omega

variable {K : Type*} [Field K]

theorem threeTwo_scalar_lift_degree (q : ℕ)
    (M : Matrix (Fin (3*q+2)) (Fin (3*q+2)) K[X])
    (P : Matrix (Fin 3) (Fin (3*q+2)) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (threeTwoScalarLiftMatrix q M P) (threeTwoFrameDegree q) := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (threeTwoLevel q) (threeTwoRow q j) (threeTwoFrameDegree q) (threeTwo_row_weight q)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem threeTwo_shift_scalar_lift_injective [CharZero K] (q : ℕ) :
    Function.Injective (threeTwoScalarLiftMatrix q
      (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)).mulVec := by
  change Function.Injective (Matrix.toLin' (threeTwoScalarLiftMatrix q
    (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q)*ᵥv=0 at hv
  have hentry (a : Fin 2) (i : Fin (3*q+2)) (b : Fin 3) :
      threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (i,b)) a.succ=
        if i.val=a.val ∧ b=2 then 1 else 0 := threeTwo_shift_scalarU q a i b
  have hentry1 (i : Fin (3*q+2)) (b : Fin 3) :
      threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (i,b)) 1=
        if i.val=0 ∧ b=2 then 1 else 0 := by simpa using hentry 0 i b
  have hentry2 (i : Fin (3*q+2)) (b : Fin 3) :
      threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (i,b)) 2=
        if i.val=1 ∧ b=2 then 1 else 0 := by simpa using hentry 1 i b
  have h0 := congrFun hv (.inr (0,0))
  have h1 := congrFun hv (.inr (0,2))
  have h2 := congrFun hv (.inr (1,2))
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h0
  change threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (0,0)) 0*v 0+
    (threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (0,0)) 1*v 1+
    threeTwoScalarLiftMatrix q (threeTwoShiftM (R:=K) q) (threeTwoShiftP q) (.inr (0,0)) 2*v 2)=0 at h0
  rw [threeTwo_shift_scalarU_zero,hentry1 0 0,hentry2 0 0] at h0
  have hv0 : v 0=0 := by
    have h02 : (0 : Fin 3)≠2 := by decide
    simp only [h02,and_false,if_false,zero_mul,add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by exact_mod_cast (Nat.succ_ne_zero q))
  have hv1 : v 1=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,
      hentry1,hentry2] using h1
  have hv2 : v 2=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,
      hentry1,hentry2] using h2
  funext j
  fin_cases j <;> assumption


end FD56
