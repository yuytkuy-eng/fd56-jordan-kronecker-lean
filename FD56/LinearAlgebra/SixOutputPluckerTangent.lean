/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerLinearizedRelations

/-! The fifteen sorted Plucker relations on the fifteen upper coordinates. -/

namespace FD56
open Matrix
open scoped BigOperators
variable {R : Type*} [CommRing R]
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

def sixOutputPair : Fin 15 → Fin 6 × Fin 6 :=
  ![(0,1),(0,2),(0,3),(0,4),(0,5),(1,2),(1,3),(1,4),(1,5),
    (2,3),(2,4),(2,5),(3,4),(3,5),(4,5)]

def sixOutputQuad : Fin 15 → Fin 4 → Fin 6 :=
  ![![0,1,2,3],![0,1,2,4],![0,1,2,5],![0,1,3,4],![0,1,3,5],
    ![0,1,4,5],![0,2,3,4],![0,2,3,5],![0,2,4,5],![0,3,4,5],
    ![1,2,3,4],![1,2,3,5],![1,2,4,5],![1,3,4,5],![2,3,4,5]]

def sixOutputPluckerTangent (F : Matrix (Fin 6) (Fin 6) R) :
    Matrix (Fin 15) (Fin 15) R := fun i j =>
  let q := sixOutputQuad i
  let p := sixOutputPair j
  if p=(q 0,q 1) then F (q 2) (q 3) else
  if p=(q 0,q 2) then -F (q 1) (q 3) else
  if p=(q 0,q 3) then F (q 1) (q 2) else
  if p=(q 1,q 2) then F (q 0) (q 3) else
  if p=(q 1,q 3) then -F (q 0) (q 2) else
  if p=(q 2,q 3) then F (q 0) (q 1) else 0

theorem sixOutputPluckerTangent_mulVec (F H : Matrix (Fin 6) (Fin 6) R)
    (i : Fin 15) :
    (sixOutputPluckerTangent F *ᵥ fun j => H (sixOutputPair j).1 (sixOutputPair j).2) i=
      pluckerLinearizedRelation F H
        (sixOutputQuad i 0) (sixOutputQuad i 1) (sixOutputQuad i 2) (sixOutputQuad i 3) := by
  fin_cases i <;>
    simp [sixOutputPluckerTangent,sixOutputPair,sixOutputQuad,Matrix.mulVec,dotProduct,
      Fin.sum_univ_succ,pluckerLinearizedRelation] <;> ring

theorem sixOutputPluckerTangent_map {S : Type*} [CommRing S]
    (f : R →+* S) (F : Matrix (Fin 6) (Fin 6) R) :
    sixOutputPluckerTangent (F.map f)=(sixOutputPluckerTangent F).map f := by
  funext i j
  simp only [sixOutputPluckerTangent,Matrix.map_apply]
  split_ifs <;> simp

theorem sixOutputPluckerTangent_smul (c : R) (F : Matrix (Fin 6) (Fin 6) R) :
    sixOutputPluckerTangent (c • F)=c • sixOutputPluckerTangent F := by
  funext i j
  simp only [sixOutputPluckerTangent,Matrix.smul_apply]
  split_ifs <;> simp

end FD56
