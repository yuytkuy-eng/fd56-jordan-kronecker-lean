/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ThreeOutputTwoSelectors
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Stabilizer.AffineSpecialization
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Three independent adjugate scalar lifts for the fourteen-state, three-output SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {R : Type*} [CommRing R]

def threeTwoScalarLiftMatrix (q : ℕ) (M : Matrix (Fin (3*q+2)) (Fin (3*q+2)) R)
    (P : Matrix (Fin 3) (Fin (3*q+2)) R) : Matrix (SLInput (Fin (3*q+2)) (Fin 3)) (Fin 3) R :=
  fun k j => observabilityScalarLift M P (threeTwoLevel q) (threeTwoRow q j) k

theorem threeTwoScalarLiftMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (3*q+2)) (Fin (3*q+2)) R)
    (P : Matrix (Fin 3) (Fin (3*q+2)) R) :
    (threeTwoScalarLiftMatrix q M P).map φ=threeTwoScalarLiftMatrix q (M.map φ) (P.map φ) := by
  funext k j
  have hC : ((observabilitySelectedMatrix M P (threeTwoLevel q) (threeTwoRow q j)).adjugate).map φ=
      (observabilitySelectedMatrix (M.map φ) (P.map φ) (threeTwoLevel q) (threeTwoRow q j)).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,observabilitySelectedMatrix_map]
  rcases k with ab|ab
  · have h := observabilityScalarX_map φ M P
      (observabilitySelectedMatrix M P (threeTwoLevel q) (threeTwoRow q j)).adjugate
      (threeTwoLevel q) (threeTwoRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2
  · have h := observabilityScalarU_map φ M
      (observabilitySelectedMatrix M P (threeTwoLevel q) (threeTwoRow q j)).adjugate
      (threeTwoLevel q) (threeTwoRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2

variable {K : Type*} [Field K]

theorem threeTwoScalarLiftMatrix_kernel (q : ℕ)
    (M : Matrix (Fin (3*q+2)) (Fin (3*q+2)) K[X])
    (P : Matrix (Fin 3) (Fin (3*q+2)) K[X]) (i₀ : Fin (3*q+2)) :
    slEquationMatrix M P i₀*threeTwoScalarLiftMatrix q M P=0 := by
  funext k j
  have h := observability_adjugate_scalar_equations M P
    (threeTwoLevel q) (threeTwoRow q j) (threeTwo_lower_closed q j)
  have hz : slEquationMatrix M P i₀ *ᵥ
      observabilityScalarLift M P (threeTwoLevel q) (threeTwoRow q j)=0 := by
    apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
    apply (slRadical_iff_equations _ _ _ _).mpr
    exact ⟨h.2.1,h.1,_,h.2.2⟩
  exact congrFun hz k

theorem fourteenThree_scalar_lift_degree
    (M : Matrix (Fin 14) (Fin 14) K[X]) (P : Matrix (Fin 3) (Fin 14) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (threeTwoScalarLiftMatrix 4 M P) 39 := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (threeTwoLevel 4) (threeTwoRow 4 j) 39 (by decide)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem fourteenThree_shift_scalarU_zero :
    threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (0,0)) 0=5 := by
  change observabilityScalarU (threeTwoShiftM (R:=K) 4)
    (observabilitySelectedMatrix (threeTwoShiftM 4) (threeTwoShiftP 4)
      (threeTwoLevel 4) (threeTwoRow 4 0)).adjugate
      (threeTwoLevel 4) (threeTwoRow 4 0) 0 0=(5 : K)
  rw [threeTwo_shift_selected_zero,Matrix.adjugate_one]
  norm_num [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,observabilityScalarColumn,
    threeTwoShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,threeTwoLevel,threeTwoRow,
    Fin.sum_univ_succ,Matrix.one_apply]

theorem fourteenThree_shift_scalar_lift_injective [CharZero K] :
    Function.Injective (threeTwoScalarLiftMatrix 4
      (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)).mulVec := by
  change Function.Injective (Matrix.toLin' (threeTwoScalarLiftMatrix 4
    (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4)*ᵥv=0 at hv
  have hentry (a : Fin 2) (i : Fin 14) (b : Fin 3) :
      threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (i,b)) a.succ=
        if i.val=a.val ∧ b=2 then 1 else 0 := threeTwo_shift_scalarU 4 a i b
  have hentry1 (i : Fin 14) (b : Fin 3) :
      threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (i,b)) 1=
        if i.val=0 ∧ b=2 then 1 else 0 := by simpa using hentry 0 i b
  have hentry2 (i : Fin 14) (b : Fin 3) :
      threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (i,b)) 2=
        if i.val=1 ∧ b=2 then 1 else 0 := by simpa using hentry 1 i b
  have h0 := congrFun hv (.inr (0,0))
  have h1 := congrFun hv (.inr (0,2))
  have h2 := congrFun hv (.inr (1,2))
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h0
  change threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (0,0)) 0*v 0+
    (threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (0,0)) 1*v 1+
    threeTwoScalarLiftMatrix 4 (threeTwoShiftM (R:=K) 4) (threeTwoShiftP 4) (.inr (0,0)) 2*v 2)=0 at h0
  rw [fourteenThree_shift_scalarU_zero,hentry1 0 0,hentry2 0 0] at h0
  have hv0 : v 0=0 := by
    have h02 : (0 : Fin 3)≠2 := by decide
    simp only [h02,and_false,if_false,zero_mul,add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by norm_num)
  have hv1 : v 1=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,
      hentry1,hentry2] using h1
  have hv2 : v 2=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,
      hentry1,hentry2] using h2
  funext j
  fin_cases j <;> assumption

end FD56
