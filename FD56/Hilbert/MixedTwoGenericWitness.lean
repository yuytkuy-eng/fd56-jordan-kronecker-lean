/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MixedPolynomialWitness
import FD56.Hilbert.MixedTwoQuadraticScalarWitness

/-! The quadratic high-row obstruction for mixed auxiliary degrees two and three. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K : Type*} [Field K]

theorem genericMixedTwoWitness_quadratic_scalar_obstruction (u v : ℕ)
    (hv : 0 < v) (hvu : v ≤ u)
    (E : Matrix (Fin v) (MixedScalarRows 2 (Fin u) (Fin v)) (MixedWitnessField K 2 u v)[X])
    (c : (MixedWitnessField K 2 u v)[X]) (hE : DegreeBound E 2) (hc : c.natDegree ≤ 7)
    (hr : E*genericMixedWitness K 2 u v = (-c) •
      (mixedScalarHighIdentity : Matrix (Fin v) (Fin u ⊕ Fin v) (MixedWitnessField K 2 u v)[X]))
    (ht : ∀ j : Fin (8-v*(u-v)), c.coeff (v*(u-v)+j.val) = 0) : E = 0 ∧ c = 0 := by
  obtain ⟨W,hW,_,_,hz⟩ := exists_mixed_two_quadratic_scalar_witness (K := K) u v hv hvu
  have hWe : ∀ x j, (W x j).natDegree ≤ mixedKernelDegree 2 u v j+2 := by
    intro x j
    have h := hW x j
    cases j <;> simpa [mixedKernelDegree,mixedColumnShift] using h
  exact genericMixedWitness_scalar_obstruction_of_witness 2 u v 2 _
    (fun j => v*(u-v)+j.val) (fun j => by have := j.isLt; dsimp; omega)
    W hWe hz E c hE hc hr ht

end FD56
