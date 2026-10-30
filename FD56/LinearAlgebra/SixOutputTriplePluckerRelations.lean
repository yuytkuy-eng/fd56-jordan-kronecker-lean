/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent

/-! The selected original Plucker quadrics vanish on every three-column
frame. Applying a derivation gives its actual tangent equations. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxHeartbeats 6000000

variable {R : Type*} [CommRing R]

theorem sixOutputTriplePluckerMinors_quadratic
    (G : Matrix (Fin 6) (Fin 3) R) (r : Fin 20) :
    sixOutputTriplePluckerQuadratic (sixOutputTriplePluckerMinors G) r=0 := by
  unfold sixOutputTriplePluckerQuadratic
  rw [sixOutputTriplePluckerTerms_eq_data]
  fin_cases r <;>
    simp [sixOutputTriplePluckerTermData,sixOutputTriplePluckerMinors,sixOutputTriple,
      Matrix.det_fin_three,Matrix.submatrix_apply] <;> ring

theorem sixOutputTriplePluckerTangent_derivation
    {B : Type*} [CommRing B] [Algebra B R]
    (D : Derivation B R R) (p : Fin 20 → R)
    (hp : ∀ r, sixOutputTriplePluckerQuadratic p r=0) :
    sixOutputTriplePluckerTangent p *ᵥ (fun j => D (p j))=0 := by
  have hlist (l : List (ℤ × (Fin 20 × Fin 20))) :
      D ((l.map (fun t => (t.1 : R)*p t.2.1*p t.2.2)).sum)=
        (l.map (fun t => (t.1 : R)*(D (p t.2.1)*p t.2.2+p t.2.1*D (p t.2.2)))).sum := by
    induction l with
    | nil => simp
    | cons t l ih =>
      simp only [List.map_cons,List.sum_cons,map_add,Derivation.leibniz,
        Derivation.map_intCast,smul_zero,smul_eq_mul,mul_zero,add_zero,ih]
      ring
  funext r
  rw [sixOutputTriplePluckerTangent_mulVec]
  have h := congrArg D (hp r)
  rw [sixOutputTriplePluckerQuadratic,hlist,map_zero] at h
  exact h

end FD56
