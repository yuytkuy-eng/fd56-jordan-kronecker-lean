/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerOutputAction
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! Transport of the weighted Plucker output action through an invertible
four-dimensional change of coordinates. -/

noncomputable section
namespace FD56
open Matrix
set_option Elab.async false
set_option maxHeartbeats 3000000

variable {R : Type*} [CommRing R]

private theorem pluckerSkewMatrix_add (F H : Fin 6 → R) :
    pluckerSkewMatrix (F+H)=pluckerSkewMatrix F+pluckerSkewMatrix H := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix,add_comm]

private theorem pluckerSkewMatrix_smul (c : R) (F : Fin 6 → R) :
    pluckerSkewMatrix (c • F)=c • pluckerSkewMatrix F := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pluckerSkewMatrix]

private theorem pluckerSkewMatrix_injective :
    Function.Injective (pluckerSkewMatrix (R:=R)) := by
  intro F H h
  have hh := congrArg (pluckerUpperCoordinates (R:=R)) h
  funext i
  have hi := congrFun hh i
  fin_cases i <;> exact hi

def pluckerOutputChange (Q : Matrix (Fin 4) (Fin 4) R) :
    (Fin 6 → R) →ₗ[R] (Fin 6 → R) where
  toFun F := pluckerUpperCoordinates (Q*pluckerSkewMatrix F*Q.transpose)
  map_add' F H := by
    rw [pluckerSkewMatrix_add,Matrix.mul_add,Matrix.add_mul,map_add]
  map_smul' c F := by
    rw [pluckerSkewMatrix_smul,Matrix.mul_smul,Matrix.smul_mul,map_smul]
    rfl

theorem pluckerOutputChange_skew (Q : Matrix (Fin 4) (Fin 4) R) (F : Fin 6 → R) :
    pluckerSkewMatrix (pluckerOutputChange Q F)=Q*pluckerSkewMatrix F*Q.transpose := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pluckerOutputChange,pluckerUpperCoordinates,pluckerSkewMatrix,
      Matrix.mul_apply,Fin.sum_univ_succ] <;> ring

theorem pluckerOutputChange_mul (Q S : Matrix (Fin 4) (Fin 4) R) (F : Fin 6 → R) :
    pluckerOutputChange Q (pluckerOutputChange S F)=pluckerOutputChange (Q*S) F := by
  apply pluckerSkewMatrix_injective
  rw [pluckerOutputChange_skew,pluckerOutputChange_skew,pluckerOutputChange_skew]
  simp only [Matrix.transpose_mul,Matrix.mul_assoc]

theorem pluckerOutputChange_one (F : Fin 6 → R) :
    pluckerOutputChange 1 F=F := by
  apply pluckerSkewMatrix_injective
  rw [pluckerOutputChange_skew,Matrix.one_mul,Matrix.transpose_one,Matrix.mul_one]

theorem pluckerOutputChange_quadric (Q : Matrix (Fin 4) (Fin 4) R) (F : Fin 6 → R) :
    pluckerQuadric (pluckerOutputChange Q F)=Q.det*pluckerQuadric F := by
  rw [Matrix.det_succ_row_zero]
  simp [pluckerOutputChange,pluckerUpperCoordinates,pluckerSkewMatrix,pluckerQuadric,
    Matrix.mul_apply,Fin.sum_univ_succ,Matrix.det_fin_three,Matrix.vecHead,Matrix.vecTail,
    Fin.succAbove]
  ring

private theorem pluckerQuadricPolar_eq (F H : Fin 6 → R) :
    pluckerQuadricPolar F H=pluckerQuadric (F+H)-pluckerQuadric F-pluckerQuadric H := by
  simp [pluckerQuadricPolar,pluckerQuadric]
  ring

theorem pluckerOutputChange_polar (Q : Matrix (Fin 4) (Fin 4) R) (F H : Fin 6 → R) :
    pluckerQuadricPolar (pluckerOutputChange Q F) (pluckerOutputChange Q H)=
      Q.det*pluckerQuadricPolar F H := by
  rw [pluckerQuadricPolar_eq,← map_add,pluckerOutputChange_quadric,
    pluckerOutputChange_quadric,pluckerOutputChange_quadric,pluckerQuadricPolar_eq]
  ring

private theorem pluckerOutputAction_skew (q : ℕ) (F : Fin 6 → R)
    (A : Matrix (Fin 4) (Fin 4) R) :
    pluckerSkewMatrix (pluckerOutputAction q F A)=
      A*pluckerSkewMatrix F+pluckerSkewMatrix F*A.transpose+
        ((q:R)*Matrix.trace A) • pluckerSkewMatrix F := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring

theorem pluckerOutputAction_covariant (q : ℕ)
    (Q S : Matrix (Fin 4) (Fin 4) R) (hSQ : S*Q=1)
    (F : Fin 6 → R) (A : Matrix (Fin 4) (Fin 4) R) :
    pluckerOutputAction q (pluckerOutputChange Q F) (Q*A*S)=
      pluckerOutputChange Q (pluckerOutputAction q F A) := by
  have htrace : Matrix.trace (Q*A*S)=Matrix.trace A := by
    rw [Matrix.trace_mul_cycle,hSQ,Matrix.one_mul]
  have ht : Q.transpose*S.transpose=1 := by
    rw [← Matrix.transpose_mul,hSQ,Matrix.transpose_one]
  have hleft : (Q*A*S)*(Q*pluckerSkewMatrix F*Q.transpose)=
      Q*(A*pluckerSkewMatrix F)*Q.transpose := by
    calc
      _ = Q*A*(S*Q)*pluckerSkewMatrix F*Q.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hSQ,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  have hright : (Q*pluckerSkewMatrix F*Q.transpose)*(Q*A*S).transpose=
      Q*(pluckerSkewMatrix F*A.transpose)*Q.transpose := by
    rw [Matrix.transpose_mul,Matrix.transpose_mul]
    calc
      _ = Q*pluckerSkewMatrix F*(Q.transpose*S.transpose)*A.transpose*Q.transpose := by
        simp only [Matrix.mul_assoc]
      _ = _ := by rw [ht,Matrix.mul_one]; simp only [Matrix.mul_assoc]
  apply pluckerSkewMatrix_injective
  rw [pluckerOutputAction_skew,pluckerOutputChange_skew,pluckerOutputChange_skew,
    pluckerOutputAction_skew,htrace,hleft,hright]
  simp only [Matrix.mul_add,Matrix.add_mul,Matrix.mul_smul,Matrix.smul_mul]

theorem pluckerOutputAction_range_of_inverse (q : ℕ)
    (Q S : Matrix (Fin 4) (Fin 4) R) (hQS : Q*S=1) (hSQ : S*Q=1)
    (H : Fin 6 → R) :
    (∃ A : Matrix (Fin 4) (Fin 4) R,
      pluckerOutputAction q (pluckerOutputChange Q standardPluckerPoint) A=H) ↔
      pluckerQuadricPolar (pluckerOutputChange Q standardPluckerPoint) H=0 := by
  constructor
  · rintro ⟨A,rfl⟩
    rw [pluckerOutputAction_quadric,pluckerOutputChange_quadric]
    simp [pluckerQuadric,standardPluckerPoint]
  · intro hH
    have hstandard : (pluckerOutputChange S H) 5=0 := by
      have h := pluckerOutputChange_polar S (pluckerOutputChange Q standardPluckerPoint) H
      rw [pluckerOutputChange_mul,hSQ,pluckerOutputChange_one,hH,mul_zero] at h
      simpa [pluckerQuadricPolar,standardPluckerPoint] using h
    obtain ⟨A,hA⟩ := (standardPluckerPoint_output_action_range q
      (pluckerOutputChange S H)).mpr hstandard
    refine ⟨Q*A*S,?_⟩
    rw [pluckerOutputAction_covariant q Q S hSQ, hA,
      pluckerOutputChange_mul,hQS,pluckerOutputChange_one]

end FD56
