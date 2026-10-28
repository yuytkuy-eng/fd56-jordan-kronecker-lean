/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PluckerOutputAction
import Mathlib.LinearAlgebra.Matrix.ToLin

/-! Unit scalar factors preserve the full output-action image. A matrix whose
row image contains these output variations and satisfies the polar relation
therefore generates the entire polynomial tangent module. -/

noncomputable section
namespace FD56
open Matrix

variable {R : Type*} [CommRing R]

def pluckerPolarRow (F : Fin 6 → R) : Matrix Unit (Fin 6) R :=
  fun _ => ![F 5,-F 4,F 3,F 2,-F 1,F 0]

theorem pluckerPolarRow_mulVec (F H : Fin 6 → R) :
    (pluckerPolarRow F *ᵥ H) ()=pluckerQuadricPolar F H := by
  simp [pluckerPolarRow,Matrix.mulVec,dotProduct,Fin.sum_univ_succ,pluckerQuadricPolar]
  ring

theorem pluckerOutputAction_smul (q : ℕ) (c : R) (F : Fin 6 → R)
    (A : Matrix (Fin 4) (Fin 4) R) :
    pluckerOutputAction q (c • F) A=c • pluckerOutputAction q F A := by
  ext i
  fin_cases i <;>
    simp [pluckerOutputAction,pluckerUpperCoordinates,pluckerSkewMatrix,
      Matrix.mul_apply,Fin.sum_univ_succ,Matrix.vecHead,Matrix.vecTail] <;> ring

private theorem polar_smul_left (c : R) (F H : Fin 6 → R) :
    pluckerQuadricPolar (c • F) H=c*pluckerQuadricPolar F H := by
  simp [pluckerQuadricPolar]
  ring

private theorem polar_smul_right (c : R) (F H : Fin 6 → R) :
    pluckerQuadricPolar F (c • H)=c*pluckerQuadricPolar F H := by
  simp [pluckerQuadricPolar]
  ring

theorem pluckerOutputAction_unit_smul_range (q : ℕ) (c : Rˣ) (F : Fin 6 → R)
    (hgen : ∀ H : Fin 6 → R,
      (∃ A : Matrix (Fin 4) (Fin 4) R, pluckerOutputAction q F A=H) ↔
        pluckerQuadricPolar F H=0) (H : Fin 6 → R) :
    (∃ A : Matrix (Fin 4) (Fin 4) R, pluckerOutputAction q ((c:R) • F) A=H) ↔
      pluckerQuadricPolar ((c:R) • F) H=0 := by
  constructor
  · rintro ⟨A,rfl⟩
    rw [pluckerOutputAction_smul,polar_smul_left,polar_smul_right,
      (hgen _).mp ⟨A,rfl⟩,mul_zero,mul_zero]
  · intro hH
    have hz : pluckerQuadricPolar F H=0 := by
      rw [polar_smul_left] at hH
      have h := congrArg (fun x => (↑c⁻¹ : R)*x) hH
      simpa only [← mul_assoc,Units.inv_mul,mul_one,one_mul,mul_zero] using h
    have hi : pluckerQuadricPolar F ((↑c⁻¹:R) • H)=0 := by
      rw [polar_smul_right,hz,mul_zero]
    obtain ⟨A,hA⟩ := (hgen _).mpr hi
    refine ⟨A,?_⟩
    rw [pluckerOutputAction_smul,hA,smul_smul,Units.mul_inv,one_smul]

theorem plucker_gradient_row_range {n : Type*} [Fintype n] [DecidableEq n]
    (q : ℕ) (F : Fin 6 → R) (Z : Matrix n (Fin 6) R)
    (hrelation : pluckerPolarRow F*Z.transpose=0)
    (houtput : ∀ A : Matrix (Fin 4) (Fin 4) R,
      ∃ u : n → R, Z.transpose *ᵥ u=pluckerOutputAction q F A)
    (hgen : ∀ H : Fin 6 → R,
      (∃ A : Matrix (Fin 4) (Fin 4) R, pluckerOutputAction q F A=H) ↔
        pluckerQuadricPolar F H=0) :
    LinearMap.range (Matrix.toLin' Z.transpose)=LinearMap.ker (Matrix.toLin' (pluckerPolarRow F)) := by
  apply le_antisymm
  · rintro H ⟨u,rfl⟩
    change pluckerPolarRow F *ᵥ (Z.transpose *ᵥ u)=0
    rw [Matrix.mulVec_mulVec,hrelation,Matrix.zero_mulVec]
  · intro H hH
    have hz : pluckerQuadricPolar F H=0 := by
      rw [← pluckerPolarRow_mulVec]
      exact congrFun hH ()
    obtain ⟨A,hA⟩ := (hgen H).mpr hz
    obtain ⟨u,hu⟩ := houtput A
    exact ⟨u,hu.trans hA⟩

end FD56
