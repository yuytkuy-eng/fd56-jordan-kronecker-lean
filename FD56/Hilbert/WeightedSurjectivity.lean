/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.WeightedCoefficients

/-! Surjective finite coefficient maps give polynomial lifts with the
specified coordinate degree bounds. -/

noncomputable section
namespace FD56
open Matrix Polynomial

variable {K a b : Type*} [Field K] [Fintype b]

theorem weighted_coefficient_surjective_lift
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hP : ∀ i j, (P i j).natDegree + g j ≤ h i)
    (hs : Function.Surjective (weightedCoefficientMatrix P g h).mulVec)
    (w : a → K[X]) (hw : ∀ i, (w i).natDegree ≤ h i) :
    ∃ v : b → K[X], (∀ j, (v j).natDegree ≤ g j) ∧ P *ᵥ v = w := by
  classical
  obtain ⟨v, hv⟩ := hs (fun ik => (w ik.1).coeff ik.2.val)
  refine ⟨weightedCoefficientPolynomial g v, weightedCoefficientPolynomial_degree g v, ?_⟩
  funext i
  apply Polynomial.ext
  intro k
  by_cases hk : k < h i + 1
  · have he := congrFun hv ⟨i, ⟨k, hk⟩⟩
    simpa only [weightedCoefficientMatrix_mulVec] using he
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt
      (lt_of_le_of_lt (weighted_polynomial_mulVec_degree P g h hP _
        (weightedCoefficientPolynomial_degree g v) i) (by omega)),
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hw i) (by omega))]

theorem weighted_coefficient_surjective_of_lifts
    [Fintype a] [DecidableEq a]
    (P : Matrix a b K[X]) (g : b → ℕ) (h : a → ℕ)
    (hlift : ∀ w : a → K[X], (∀ i, (w i).natDegree ≤ h i) →
      ∃ v : b → K[X], (∀ j, (v j).natDegree ≤ g j) ∧ P *ᵥ v = w) :
    Function.Surjective (weightedCoefficientMatrix P g h).mulVec := by
  classical
  intro w
  obtain ⟨v, hv, he⟩ := hlift (weightedCoefficientPolynomial h w)
    (weightedCoefficientPolynomial_degree h w)
  refine ⟨fun jl => (v jl.1).coeff jl.2.val, ?_⟩
  have hrec : weightedCoefficientPolynomial g (fun jl => (v jl.1).coeff jl.2.val) = v := by
    funext j
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
      (p := v j) (n := g j + 1) (by have := hv j; omega)
  funext ik
  rw [weightedCoefficientMatrix_mulVec, hrec, he]
  simp [weightedCoefficientPolynomial]

end FD56
