/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ThreeOutputOneSelectors
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Stabilizer.AffineSpecialization
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Three independent adjugate scalar lifts for the ten-state, three-output SL pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable {R : Type*} [CommRing R]

def threeOneScalarLiftMatrix (q : ℕ) (M : Matrix (Fin (3*q+1)) (Fin (3*q+1)) R)
    (P : Matrix (Fin 3) (Fin (3*q+1)) R) : Matrix (SLInput (Fin (3*q+1)) (Fin 3)) (Fin 3) R :=
  fun k j => observabilityScalarLift M P (threeOneLevel q) (threeOneRow q j) k

theorem threeOneScalarLiftMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (3*q+1)) (Fin (3*q+1)) R)
    (P : Matrix (Fin 3) (Fin (3*q+1)) R) :
    (threeOneScalarLiftMatrix q M P).map φ=threeOneScalarLiftMatrix q (M.map φ) (P.map φ) := by
  funext k j
  have hC : ((observabilitySelectedMatrix M P (threeOneLevel q) (threeOneRow q j)).adjugate).map φ=
      (observabilitySelectedMatrix (M.map φ) (P.map φ) (threeOneLevel q) (threeOneRow q j)).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,observabilitySelectedMatrix_map]
  rcases k with ab|ab
  · have h := observabilityScalarX_map φ M P
      (observabilitySelectedMatrix M P (threeOneLevel q) (threeOneRow q j)).adjugate
      (threeOneLevel q) (threeOneRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2
  · have h := observabilityScalarU_map φ M
      (observabilitySelectedMatrix M P (threeOneLevel q) (threeOneRow q j)).adjugate
      (threeOneLevel q) (threeOneRow q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2

variable {K : Type*} [Field K]

theorem threeOneScalarLiftMatrix_kernel (q : ℕ)
    (M : Matrix (Fin (3*q+1)) (Fin (3*q+1)) K[X])
    (P : Matrix (Fin 3) (Fin (3*q+1)) K[X]) (i₀ : Fin (3*q+1)) :
    slEquationMatrix M P i₀*threeOneScalarLiftMatrix q M P=0 := by
  funext k j
  have h := observability_adjugate_scalar_equations M P
    (threeOneLevel q) (threeOneRow q j) (threeOne_lower_closed q j)
  have hz : slEquationMatrix M P i₀ *ᵥ
      observabilityScalarLift M P (threeOneLevel q) (threeOneRow q j)=0 := by
    apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
    apply (slRadical_iff_equations _ _ _ _).mpr
    exact ⟨h.2.1,h.1,_,h.2.2⟩
  exact congrFun hz k

theorem tenThree_scalar_lift_degree
    (M : Matrix (Fin 10) (Fin 10) K[X]) (P : Matrix (Fin 3) (Fin 10) K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) :
    DegreeBound (threeOneScalarLiftMatrix 3 M P) 21 := by
  intro k j
  obtain ⟨hX,hU,_⟩ := observability_adjugate_solution_degree M P hM hP
    (threeOneLevel 3) (threeOneRow 3 j) 21 (by decide)
  rcases k with ab|ab
  · exact hX ab.1 ab.2
  · exact hU ab.1 ab.2

theorem tenThree_shift_scalarU_zero :
    threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3) (.inr (0,0)) 0=4 := by
  change observabilityScalarU (threeOneShiftM (R:=K) 3)
    (observabilitySelectedMatrix (threeOneShiftM 3) (threeOneShiftP 3)
      (threeOneLevel 3) (threeOneRow 3 0)).adjugate
      (threeOneLevel 3) (threeOneRow 3 0) 0 0=(4 : K)
  rw [threeOne_shift_selected_zero,Matrix.adjugate_one]
  norm_num [observabilityScalarU,Matrix.sum_apply,Matrix.mul_apply,observabilityScalarColumn,
    threeOneShiftM,finiteShiftMatrix_pow,finiteShiftMatrix,threeOneLevel,threeOneRow,
    Fin.sum_univ_succ,Matrix.one_apply]

theorem tenThree_shift_scalar_lift_injective [CharZero K] :
    Function.Injective (threeOneScalarLiftMatrix 3
      (threeOneShiftM (R:=K) 3) (threeOneShiftP 3)).mulVec := by
  change Function.Injective (Matrix.toLin' (threeOneScalarLiftMatrix 3
    (threeOneShiftM (R:=K) 3) (threeOneShiftP 3)))
  apply (LinearMap.ker_eq_bot).mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  change threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3)*ᵥv=0 at hv
  have hentry (a b : Fin 3) (ha : a≠0) :
      threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3) (.inr (0,b)) a=
        if b=a then 1 else 0 := threeOne_shift_scalarU 3 a b ha
  have h0 := congrFun hv (.inr (0,0))
  have h1 := congrFun hv (.inr (0,1))
  have h2 := congrFun hv (.inr (0,2))
  simp only [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,Fin.sum_univ_zero,add_zero] at h0
  change threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3) (.inr (0,0)) 0*v 0+
    (threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3) (.inr (0,0)) 1*v 1+
    threeOneScalarLiftMatrix 3 (threeOneShiftM (R:=K) 3) (threeOneShiftP 3) (.inr (0,0)) 2*v 2)=0 at h0
  rw [tenThree_shift_scalarU_zero,hentry 1 0 (by decide),hentry 2 0 (by decide)] at h0
  have hv0 : v 0=0 := by
    have h01 : (0 : Fin 3)≠1 := by decide
    have h02 : (0 : Fin 3)≠2 := by decide
    simp only [h01,h02,if_false,zero_mul,add_zero] at h0
    exact (mul_eq_zero.mp h0).resolve_left (by norm_num)
  have hv1 : v 1=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,hentry] using h1
  have hv2 : v 2=0 := by
    simpa [Matrix.mulVec,dotProduct,Fin.sum_univ_succ,hv0,hentry] using h2
  funext j
  fin_cases j <;> assumption

end FD56
