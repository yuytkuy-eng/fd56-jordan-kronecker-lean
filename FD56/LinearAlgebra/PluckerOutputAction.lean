/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Tactic

/-! The determinant-weighted output action on six Plucker coordinates. At
the standard two-plane its image is the full tangent hyperplane over every
commutative ring; the radial lift uses (q+1)-q=1, not division by a weight. -/

noncomputable section
namespace FD56
open Matrix

variable {R : Type*} [CommRing R]

def pluckerSkewMatrix (F : Fin 6 → R) : Matrix (Fin 4) (Fin 4) R :=
  ![![0,F 0,F 1,F 2],![-F 0,0,F 3,F 4],![-F 1,-F 3,0,F 5],![-F 2,-F 4,-F 5,0]]

def pluckerUpperCoordinates : Matrix (Fin 4) (Fin 4) R →ₗ[R] (Fin 6 → R) where
  toFun A := ![A 0 1,A 0 2,A 0 3,A 1 2,A 1 3,A 2 3]
  map_add' A B := by ext i; fin_cases i <;> rfl
  map_smul' c A := by ext i; fin_cases i <;> rfl

def pluckerQuadric (F : Fin 6 → R) : R := F 0*F 5-F 1*F 4+F 2*F 3

def pluckerQuadricPolar (F H : Fin 6 → R) : R :=
  F 0*H 5+H 0*F 5-F 1*H 4-H 1*F 4+F 2*H 3+H 2*F 3

def pluckerOutputAction (q : ℕ) (F : Fin 6 → R) :
    Matrix (Fin 4) (Fin 4) R →ₗ[R] (Fin 6 → R) where
  toFun A := pluckerUpperCoordinates (A*pluckerSkewMatrix F+pluckerSkewMatrix F*A.transpose)+
    ((q:R)*Matrix.trace A) • F
  map_add' A B := by
    simp only [Matrix.add_mul,Matrix.transpose_add,Matrix.mul_add,Matrix.trace_add,
      mul_add,add_smul]
    rw [show A*pluckerSkewMatrix F+B*pluckerSkewMatrix F+
        (pluckerSkewMatrix F*A.transpose+pluckerSkewMatrix F*B.transpose)=
      (A*pluckerSkewMatrix F+pluckerSkewMatrix F*A.transpose)+
        (B*pluckerSkewMatrix F+pluckerSkewMatrix F*B.transpose) by abel]
    rw [map_add]
    abel
  map_smul' c A := by
    simp only [Matrix.smul_mul,Matrix.transpose_smul,Matrix.mul_smul,Matrix.trace_smul,
      ← smul_add,map_smul]
    ext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul,RingHom.id_apply]
    ring

def standardPluckerPoint : Fin 6 → R := ![1,0,0,0,0,0]

def standardPluckerTangentLift (H : Fin 6 → R) : Matrix (Fin 4) (Fin 4) R :=
  ![![H 0,0,0,0],![0,0,0,0],![-H 3,H 1,-H 0,0],![-H 4,H 2,0,0]]

theorem pluckerOutputAction_quadric (q : ℕ) (F : Fin 6 → R)
    (A : Matrix (Fin 4) (Fin 4) R) :
    pluckerQuadricPolar F (pluckerOutputAction q F A)=
      ((2*q+1:R)*Matrix.trace A)*pluckerQuadric F := by
  simp [pluckerQuadricPolar,pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,
    pluckerQuadric,Matrix.mul_apply,Matrix.trace,Fin.sum_univ_succ,
    Matrix.vecHead,Matrix.vecTail]
  ring

theorem standardPluckerTangentLift_action (q : ℕ) (H : Fin 6 → R) :
    pluckerOutputAction q standardPluckerPoint (standardPluckerTangentLift H)=
      ![H 0,H 1,H 2,H 3,H 4,0] := by
  ext i
  fin_cases i <;>
    simp [pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,
      standardPluckerPoint,standardPluckerTangentLift,Matrix.mul_apply,
      Matrix.trace,Fin.sum_univ_succ]

theorem standardPluckerPoint_output_action_range (q : ℕ) (H : Fin 6 → R) :
    (∃ A : Matrix (Fin 4) (Fin 4) R,
      pluckerOutputAction q standardPluckerPoint A=H) ↔ H 5=0 := by
  constructor
  · rintro ⟨A,rfl⟩
    simp [pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,
      standardPluckerPoint,Matrix.mul_apply,Fin.sum_univ_succ]
  · intro h
    refine ⟨standardPluckerTangentLift H,?_⟩
    rw [standardPluckerTangentLift_action]
    ext i
    fin_cases i <;> simp [h]

end FD56
