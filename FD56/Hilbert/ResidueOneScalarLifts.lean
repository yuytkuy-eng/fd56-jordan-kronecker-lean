/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ResidueOneSelectors
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Stabilizer.AffineSpecialization
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Adjugate scalar lifts for state count mq+1 and m positive outputs. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable (m : ℕ) [NeZero m]
variable {R : Type*} [CommRing R]

def residueOneScalarLiftMatrix (q : ℕ) (M : Matrix (Fin (m*q+1)) (Fin (m*q+1)) R)
    (P : Matrix (Fin m) (Fin (m*q+1)) R) : Matrix (SLInput (Fin (m*q+1)) (Fin m)) (Fin m) R :=
  fun k j => observabilityScalarLift M P (residueOneLevel m q) (residueOneRow m q j) k

theorem residueOneScalarLiftMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin (m*q+1)) (Fin (m*q+1)) R)
    (P : Matrix (Fin m) (Fin (m*q+1)) R) :
    (residueOneScalarLiftMatrix m q M P).map φ=residueOneScalarLiftMatrix m q (M.map φ) (P.map φ) := by
  funext k j
  have hC : ((observabilitySelectedMatrix M P (residueOneLevel m q) (residueOneRow m q j)).adjugate).map φ=
      (observabilitySelectedMatrix (M.map φ) (P.map φ) (residueOneLevel m q) (residueOneRow m q j)).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,observabilitySelectedMatrix_map]
  rcases k with ab|ab
  · have h := observabilityScalarX_map φ M P
      (observabilitySelectedMatrix M P (residueOneLevel m q) (residueOneRow m q j)).adjugate
      (residueOneLevel m q) (residueOneRow m q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2
  · have h := observabilityScalarU_map φ M
      (observabilitySelectedMatrix M P (residueOneLevel m q) (residueOneRow m q j)).adjugate
      (residueOneLevel m q) (residueOneRow m q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2

variable {K : Type*} [Field K]

theorem residueOneScalarLiftMatrix_kernel (q : ℕ)
    (M : Matrix (Fin (m*q+1)) (Fin (m*q+1)) K[X])
    (P : Matrix (Fin m) (Fin (m*q+1)) K[X]) (i₀ : Fin (m*q+1)) :
    slEquationMatrix M P i₀*residueOneScalarLiftMatrix m q M P=0 := by
  funext k j
  have h := observability_adjugate_scalar_equations M P
    (residueOneLevel m q) (residueOneRow m q j) (residueOne_lower_closed m q j)
  have hz : slEquationMatrix M P i₀ *ᵥ
      observabilityScalarLift M P (residueOneLevel m q) (residueOneRow m q j)=0 := by
    apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
    apply (slRadical_iff_equations _ _ _ _).mpr
    exact ⟨h.2.1,h.1,_,h.2.2⟩
  exact congrFun hz k

end FD56
