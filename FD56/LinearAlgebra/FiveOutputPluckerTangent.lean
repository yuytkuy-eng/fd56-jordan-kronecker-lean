/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerLinearizedRelations

/-! The five sorted Plucker relations on the ten upper coordinates. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R]

def fiveOutputPair : Fin 10 → Fin 5 × Fin 5 :=
  ![(0,1),(0,2),(0,3),(0,4),(1,2),(1,3),(1,4),(2,3),(2,4),(3,4)]

def fiveOutputQuad : Fin 5 → Fin 4 → Fin 5 :=
  ![![0,1,2,3],![0,1,2,4],![0,1,3,4],![0,2,3,4],![1,2,3,4]]

def fiveOutputPluckerTangent (F : Matrix (Fin 5) (Fin 5) R) :
    Matrix (Fin 5) (Fin 10) R :=
  ![![F 2 3,-F 1 3,F 1 2,0,F 0 3,-F 0 2,0,F 0 1,0,0],
    ![F 2 4,-F 1 4,0,F 1 2,F 0 4,0,-F 0 2,0,F 0 1,0],
    ![F 3 4,0,-F 1 4,F 1 3,0,F 0 4,-F 0 3,0,0,F 0 1],
    ![0,F 3 4,-F 2 4,F 2 3,0,0,0,F 0 4,-F 0 3,F 0 2],
    ![0,0,0,0,F 3 4,-F 2 4,F 2 3,F 1 4,-F 1 3,F 1 2]]

theorem fiveOutputPluckerTangent_mulVec (F H : Matrix (Fin 5) (Fin 5) R)
    (i : Fin 5) :
    (fiveOutputPluckerTangent F *ᵥ fun j => H (fiveOutputPair j).1 (fiveOutputPair j).2) i=
      pluckerLinearizedRelation F H
        (fiveOutputQuad i 0) (fiveOutputQuad i 1) (fiveOutputQuad i 2) (fiveOutputQuad i 3) := by
  fin_cases i <;>
    simp [fiveOutputPluckerTangent,fiveOutputPair,fiveOutputQuad,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,pluckerLinearizedRelation] <;> ring

end FD56
