/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ObservabilityScalarFunctional
import FD56.Hilbert.OneOutputSLNullity
import FD56.Hilbert.OneOutputWeight
import FD56.Stabilizer.GenericObservabilitySeparable

/-! Separability of the scalar observability determinant excludes every smaller SL degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem one_output_observability_lower_closed (N : ℕ) :
    ∀ k : Fin N, ∀ s, s<k.val → ∀ a : Fin 1,
      ∃ l : Fin N, l.val=s ∧ (0 : Fin 1)=a := by
  intro k s hs a
  exact ⟨⟨s,lt_trans hs k.isLt⟩,rfl,Subsingleton.elim _ _⟩

theorem generic_one_output_sl_critical_vanishing {K : Type*} [Field K]
    (N : ℕ) (hN : 2 ≤ N) :
    slHilbert (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)) (oneOutputWeight N-2)=0 := by
  obtain ⟨hdeg,hsep⟩ := generic_scalar_observability_separable K N
  apply slHilbert_zero_of_separable_observability _ _ (⟨0,by omega⟩ : Fin N)
    (oneOutputWeight N-2) (genericAffineSquare_degree _ _ _) (genericAffineRows_degree _ _ _)
    Fin.val (fun _ => (0 : Fin 1)) (one_output_observability_lower_closed N) hsep
  · rw [hdeg]
    change oneOutputWeight N-2+1 < oneOutputWeight N
    have h := oneOutputWeight_three_le N hN
    omega
  · exact generic_one_output_gl_injective N hN

end FD56
