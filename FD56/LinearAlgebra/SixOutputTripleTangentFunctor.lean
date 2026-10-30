/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SixOutputTriplePluckerTangent

/-! Ring maps and scalar multiplication for the actual three-column tangent matrix. -/

namespace FD56
open Matrix
set_option Elab.async false

theorem sixOutputTriplePluckerTangent_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (p : Fin 20 → R) :
    (sixOutputTriplePluckerTangent p).map φ=
      sixOutputTriplePluckerTangent (fun i => φ (p i)) := by
  apply Matrix.ext
  intro i j
  simp only [sixOutputTriplePluckerTangent, Matrix.map_apply]
  induction sixOutputTriplePluckerTerms i with
  | nil => simp
  | cons t l ih => simp [ih, apply_ite φ]

theorem sixOutputTriplePluckerTangent_smul {R : Type*} [CommRing R]
    (c : R) (p : Fin 20 → R) :
    sixOutputTriplePluckerTangent (c • p)=c • sixOutputTriplePluckerTangent p := by
  apply Matrix.ext
  intro i j
  simp only [sixOutputTriplePluckerTangent, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply]
  induction sixOutputTriplePluckerTerms i with
  | nil => simp
  | cons t l ih =>
    simp only [List.map_cons,List.sum_cons,ih]
    split_ifs <;> ring

theorem sixOutputTriplePluckerMinors_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (G : Matrix (Fin 6) (Fin 3) R) :
    sixOutputTriplePluckerMinors (G.map φ)=fun i => φ (sixOutputTriplePluckerMinors G i) := by
  funext i
  exact (φ.map_det _).symm

theorem sixOutputTriplePluckerMinors_smul {R : Type*} [CommRing R]
    (c : R) (G : Matrix (Fin 6) (Fin 3) R) :
    sixOutputTriplePluckerMinors (c • G)=c^3 • sixOutputTriplePluckerMinors G := by
  funext i
  exact Matrix.det_smul _ c

theorem sixOutputTripleTangent_frame_map {R S : Type*} [CommRing R] [CommRing S]
    (φ : R →+* S) (G : Matrix (Fin 6) (Fin 3) R) :
    (sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G)).map φ=
      sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors (G.map φ)) := by
  rw [sixOutputTriplePluckerTangent_map,sixOutputTriplePluckerMinors_map]

theorem sixOutputTripleTangent_frame_smul {R : Type*} [CommRing R]
    (c : R) (G : Matrix (Fin 6) (Fin 3) R) :
    sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors (c • G))=
      c^3 • sixOutputTriplePluckerTangent (sixOutputTriplePluckerMinors G) := by
  rw [sixOutputTriplePluckerMinors_smul,sixOutputTriplePluckerTangent_smul]

end FD56
