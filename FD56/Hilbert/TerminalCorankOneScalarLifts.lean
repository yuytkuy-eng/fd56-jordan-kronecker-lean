/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.TerminalCorankOneSelectors
import FD56.Stabilizer.ObservabilityScalarAdjugateMap
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.ObservabilityScalarAdjugateDegree
import FD56.Stabilizer.AffineSpecialization
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Adjugate scalar lifts for terminal corank one at every output count. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 2048
variable (s : ℕ)
variable {R : Type*} [CommRing R]

def terminalOneScalarLiftMatrix (q : ℕ) (M : Matrix (Fin ((s+2)*q+s+1)) (Fin ((s+2)*q+s+1)) R)
    (P : Matrix (Fin (s+2)) (Fin ((s+2)*q+s+1)) R) : Matrix (SLInput (Fin ((s+2)*q+s+1)) (Fin (s+2))) (Fin (s+2)) R :=
  fun k j => observabilityScalarLift M P (terminalOneLevel s q) (terminalOneRow s q j) k

theorem terminalOneScalarLiftMatrix_map {S : Type*} [CommRing S] (φ : R →+* S)
    (q : ℕ) (M : Matrix (Fin ((s+2)*q+s+1)) (Fin ((s+2)*q+s+1)) R)
    (P : Matrix (Fin (s+2)) (Fin ((s+2)*q+s+1)) R) :
    (terminalOneScalarLiftMatrix s q M P).map φ=terminalOneScalarLiftMatrix s q (M.map φ) (P.map φ) := by
  funext k j
  have hC : ((observabilitySelectedMatrix M P (terminalOneLevel s q) (terminalOneRow s q j)).adjugate).map φ=
      (observabilitySelectedMatrix (M.map φ) (P.map φ) (terminalOneLevel s q) (terminalOneRow s q j)).adjugate := by
    rw [← RingHom.mapMatrix_apply,φ.map_adjugate,RingHom.mapMatrix_apply,observabilitySelectedMatrix_map]
  rcases k with ab|ab
  · have h := observabilityScalarX_map φ M P
      (observabilitySelectedMatrix M P (terminalOneLevel s q) (terminalOneRow s q j)).adjugate
      (terminalOneLevel s q) (terminalOneRow s q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2
  · have h := observabilityScalarU_map φ M
      (observabilitySelectedMatrix M P (terminalOneLevel s q) (terminalOneRow s q j)).adjugate
      (terminalOneLevel s q) (terminalOneRow s q j)
    rw [hC] at h
    exact congrFun (congrFun h ab.1) ab.2

variable {K : Type*} [Field K]

theorem terminalOneScalarLiftMatrix_kernel (q : ℕ)
    (M : Matrix (Fin ((s+2)*q+s+1)) (Fin ((s+2)*q+s+1)) K[X])
    (P : Matrix (Fin (s+2)) (Fin ((s+2)*q+s+1)) K[X]) (i₀ : Fin ((s+2)*q+s+1)) :
    slEquationMatrix M P i₀*terminalOneScalarLiftMatrix s q M P=0 := by
  funext k j
  have h := observability_adjugate_scalar_equations M P
    (terminalOneLevel s q) (terminalOneRow s q j) (terminalOne_lower_closed s q j)
  have hz : slEquationMatrix M P i₀ *ᵥ
      observabilityScalarLift M P (terminalOneLevel s q) (terminalOneRow s q j)=0 := by
    apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
    apply (slRadical_iff_equations _ _ _ _).mpr
    exact ⟨h.2.1,h.1,_,h.2.2⟩
  exact congrFun hz k

end FD56
