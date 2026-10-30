/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericSixOutputTripleRepresentation
import FD56.LinearAlgebra.ThreeColumnPluckerDominance

/-! The actual middle-remainder minors faithfully evaluate the universal
equal-degree three-column minor coefficient algebra in characteristic zero. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false

variable {K : Type*} [Field K] [CharZero K]

theorem generic_six_output_triple_specialization_faithful (q : ℕ) (hq : 0<q) :
    ∃ G : Matrix (Fin 6) (Fin 3)
        (AffineCoefficientField K (MatrixParameters (Fin (6*q+3)) (Fin 6)))[X],
      (∀ i j, (G i j).natDegree≤(q+1)^2) ∧
      (∀ row : Fin 3 → Fin 6,
        interiorFullMinor 3 3 q (genericAffineSquare K (Fin (6*q+3)) (Fin 6))
          (genericAffineRows K (Fin (6*q+3)) (Fin 6)) row=
          pluckerMinorVector G row) ∧
      Function.Injective (threeColumnMinorSpecialization ((q+1)^2)
        (threeColumnCoefficientEvaluation (K:=K) ((q+1)^2) G)) := by
  obtain ⟨G,hG,hfull⟩ := generic_six_output_triple_minor_realization (K:=K) q hq
  refine ⟨G,hG,hfull,?_⟩
  let pivot : Fin 3 ↪ Fin 6 := ⟨Fin.castAdd 3,Fin.castAdd_injective 3 3⟩
  apply three_column_coefficient_evaluation_faithful ((q+1)^2) pivot G hG
    (interiorTerminalRow 3 3)
  have he : (fun z => pluckerMinorVector G (interiorTerminalRow 3 3 z))=
      genericInteriorMinorVector (K:=K) 3 3 q := by
    funext z
    have hh := hfull (interiorTerminalRow 3 3 z)
    simpa only [interiorFullMinor,interiorFullRow_selected] using hh.symm
  rw [he]
  have h := generic_interior_minor_derivation_rank_lower_of_weight (K:=K)
    3 3 q hq (3*(q+1)^2) (by ring)
  simp only [Fintype.card_fin]
  exact le_trans (by omega) h

end FD56
