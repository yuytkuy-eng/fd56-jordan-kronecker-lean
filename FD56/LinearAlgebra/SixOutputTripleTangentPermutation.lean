/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent

/-! The endpoint-block swap preserves the closed system of twenty triple
Plucker tangent equations. Its action on increasing triple coordinates is unsigned. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxHeartbeats 4000000
set_option maxRecDepth 4000

def sixOutputTripleTailSwap : Fin 6 → Fin 6 := ![3,4,5,0,1,2]

def sixOutputTripleTailSwapIndex : Fin 20 → Fin 20 :=
  ![19,7,13,16,8,14,17,1,4,10,9,15,18,2,5,11,3,6,12,0]

def sixOutputTripleTailSwapCoordinates {V : Type*} (z : Fin 20 → V) : Fin 20 → V :=
  z ∘ sixOutputTripleTailSwapIndex

def sixOutputTripleTailSwapEquations {V : Type*} [Neg V] (z : Fin 20 → V) : Fin 20 → V :=
  ![z 11,z 13,z 15,z 12,z 14,z 16,-z 10,z 17,z 18,z 19,-z 6,z 0,z 3,z 1,z 4,z 2,z 5,z 7,z 8,z 9]

theorem sixOutputTripleTailSwap_involutive : Function.Involutive sixOutputTripleTailSwap := by
  intro i
  fin_cases i <;> rfl

theorem sixOutputTripleTailSwapCoordinates_involutive {V : Type*} :
    Function.Involutive (sixOutputTripleTailSwapCoordinates (V:=V)) := by
  intro z
  funext j
  fin_cases j <;> rfl

theorem sixOutputTriplePluckerMinors_tailSwap {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 3) R) :
    sixOutputTriplePluckerMinors (fun i j => G (sixOutputTripleTailSwap i) j)=
      sixOutputTripleTailSwapCoordinates (sixOutputTriplePluckerMinors G) := by
  funext c
  fin_cases c <;>
    simp [sixOutputTriplePluckerMinors,Matrix.det_fin_three,Matrix.submatrix_apply,
      sixOutputTriple,sixOutputTripleTailSwapCoordinates,sixOutputTripleTailSwapIndex,
      sixOutputTripleTailSwap,Function.comp_def] <;> ring

theorem sixOutputTriplePluckerTangent_tailSwap_mulVec {R : Type*} [CommRing R]
    (p z : Fin 20 → R) :
    sixOutputTriplePluckerTangent (sixOutputTripleTailSwapCoordinates p)*ᵥ
      sixOutputTripleTailSwapCoordinates z=
      sixOutputTripleTailSwapEquations (sixOutputTriplePluckerTangent p*ᵥz) := by
  funext i
  rw [sixOutputTriplePluckerTangent_mulVec]
  fin_cases i <;>
    simp only [sixOutputTripleTailSwapEquations,Matrix.cons_val_zero,Matrix.cons_val_succ,
      sixOutputTriplePluckerTangent_mulVec] <;>
    simp [sixOutputTriplePluckerLinearized,sixOutputTriplePluckerTerms_eq_data,
      sixOutputTriplePluckerTermData,sixOutputTripleTailSwapCoordinates,
      sixOutputTripleTailSwapIndex,Function.comp_def] <;> ring

theorem sixOutputTriplePluckerTangent_tailSwap_kernel {R : Type*} [CommRing R]
    (G : Matrix (Fin 6) (Fin 3) R) (z : Fin 20 → R)
    (hz : sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)*ᵥz=0) :
    sixOutputTriplePluckerTangent
      (sixOutputTriplePluckerMinors (fun i j => G (sixOutputTripleTailSwap i) j))*ᵥ
        sixOutputTripleTailSwapCoordinates z=0 := by
  rw [sixOutputTriplePluckerMinors_tailSwap,sixOutputTriplePluckerTangent_tailSwap_mulVec,hz]
  funext j
  fin_cases j <;> simp [sixOutputTripleTailSwapEquations]

end FD56
