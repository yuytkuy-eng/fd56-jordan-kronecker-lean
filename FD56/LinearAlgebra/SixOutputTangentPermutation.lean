/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputPluckerTangent

/-! The fixed row permutation exchanging endpoint pairs and its signed
action on Plucker coordinates and tangent equations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4000

def sixOutputTailSwap : Fin 6 → Fin 6 := ![2,3,0,1,4,5]

def sixOutputTailSwapCoordinates {V : Type*} [Neg V] (z : Fin 15 → V) : Fin 15 → V :=
  ![z 9,-z 1,-z 5,z 10,z 11,-z 2,-z 6,z 12,z 13,z 0,z 3,z 4,z 7,z 8,z 14]

def sixOutputTailSwapEquations {V : Type*} [Neg V] (z : Fin 15 → V) : Fin 15 → V :=
  ![z 0,z 6,z 7,z 10,z 11,z 14,z 1,z 2,-z 8,-z 12,z 3,z 4,-z 9,-z 13,z 5]

theorem sixOutputTailSwap_involutive : Function.Involutive sixOutputTailSwap := by
  intro i
  fin_cases i <;> rfl

theorem sixOutputTailSwapCoordinates_involutive {V : Type*} [AddGroup V] :
    Function.Involutive (sixOutputTailSwapCoordinates (V:=V)) := by
  intro z
  funext j
  fin_cases j <;> simp [sixOutputTailSwapCoordinates]

private def upperMatrix {R : Type*} [CommRing R] (z : Fin 15 → R) : Matrix (Fin 6) (Fin 6) R :=
  ![![0,z 0,z 1,z 2,z 3,z 4],![-z 0,0,z 5,z 6,z 7,z 8],
    ![-z 1,-z 5,0,z 9,z 10,z 11],![-z 2,-z 6,-z 9,0,z 12,z 13],
    ![-z 3,-z 7,-z 10,-z 12,0,z 14],![-z 4,-z 8,-z 11,-z 13,-z 14,0]]

private theorem upperMatrix_swap {R : Type*} [CommRing R] (z : Fin 15 → R) :
    upperMatrix (sixOutputTailSwapCoordinates z)=
      (upperMatrix z).submatrix sixOutputTailSwap sixOutputTailSwap := by
  funext i j
  fin_cases i <;> fin_cases j <;>
    simp [upperMatrix,sixOutputTailSwapCoordinates,sixOutputTailSwap]

private theorem tangent_as_relation {R : Type*} [CommRing R]
    (F : Matrix (Fin 6) (Fin 6) R) (z : Fin 15 → R) (i : Fin 15) :
    (sixOutputPluckerTangent F*ᵥz) i=pluckerLinearizedRelation F (upperMatrix z)
      (sixOutputQuad i 0) (sixOutputQuad i 1) (sixOutputQuad i 2) (sixOutputQuad i 3) := by
  have he : (fun j => upperMatrix z (sixOutputPair j).1 (sixOutputPair j).2)=z := by
    funext j
    fin_cases j <;> rfl
  calc
    _=(sixOutputPluckerTangent F*ᵥ(fun j => upperMatrix z (sixOutputPair j).1 (sixOutputPair j).2)) i := by rw [he]
    _=_ := sixOutputPluckerTangent_mulVec F (upperMatrix z) i

theorem sixOutputPluckerTangent_tailSwap_mulVec {R : Type*} [CommRing R]
    (u v : Fin 6 → R) (z : Fin 15 → R) :
    sixOutputPluckerTangent (twoColumnWedge (u ∘ sixOutputTailSwap) (v ∘ sixOutputTailSwap))*ᵥ
      sixOutputTailSwapCoordinates z =
      sixOutputTailSwapEquations (sixOutputPluckerTangent (twoColumnWedge u v)*ᵥz) := by
  funext i
  rw [tangent_as_relation,upperMatrix_swap]
  fin_cases i <;>
    simp [sixOutputTailSwapEquations,pluckerLinearizedRelation,sixOutputQuad,
      sixOutputTailSwap,upperMatrix,twoColumnWedge,Function.comp_def] <;>
    rw [tangent_as_relation] <;>
    simp [pluckerLinearizedRelation,sixOutputQuad,upperMatrix,twoColumnWedge] <;> ring

theorem sixOutputPluckerTangent_tailSwap_kernel {R : Type*} [CommRing R]
    (u v : Fin 6 → R) (z : Fin 15 → R)
    (hz : sixOutputPluckerTangent (twoColumnWedge u v)*ᵥz=0) :
    sixOutputPluckerTangent (twoColumnWedge (u ∘ sixOutputTailSwap) (v ∘ sixOutputTailSwap))*ᵥ
      sixOutputTailSwapCoordinates z=0 := by
  rw [sixOutputPluckerTangent_tailSwap_mulVec,hz]
  funext j
  fin_cases j <;> simp [sixOutputTailSwapEquations]

end FD56
