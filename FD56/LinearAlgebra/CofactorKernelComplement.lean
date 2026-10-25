/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.RectangularCofactors
import FD56.LinearAlgebra.PredictableDegree

/-! An invertible cofactor completion gives polynomial kernel coordinates. -/

namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {R : Type*} [CommRing R] {N : ℕ}

theorem cofactorCompletion_pairing
    (Z : Matrix (Fin (N + 1)) (Fin N) R) (w v : Fin (N + 1) → R) :
    rectangularCofactors Z ⬝ᵥ (cofactorCompletion Z w *ᵥ v) =
      (cofactorCompletion Z w).det * v 0 := by
  rw [dotProduct_mulVec]
  have hrow : rectangularCofactors Z ᵥ* cofactorCompletion Z w =
      Fin.cases (cofactorCompletion Z w).det (fun _ => 0) := by
    funext j
    refine Fin.cases ?_ (fun j => ?_) j
    · change (∑ i, rectangularCofactors Z i * w i) = _
      rw [cofactorCompletion_det]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    · change (∑ i, rectangularCofactors Z i * Z i j) = 0
      simpa only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm] using
        congrFun (rectangularCofactors_relation Z) j
  rw [hrow]
  simp [dotProduct, Fin.sum_univ_succ]

theorem cofactor_kernel_iff_range_of_completion_unit
    (Z : Matrix (Fin (N + 1)) (Fin N) R) (w : Fin (N + 1) → R)
    (hunit : IsUnit (cofactorCompletion Z w).det) (E : Fin (N + 1) → R) :
    rectangularCofactors Z ⬝ᵥ E = 0 ↔ ∃ c : Fin N → R, E = Z *ᵥ c := by
  constructor
  · intro hE
    have hsurj : Function.Surjective (cofactorCompletion Z w).mulVec :=
      Matrix.mulVec_surjective_iff_isUnit.mpr
        ((Matrix.isUnit_iff_isUnit_det _).mpr hunit)
    obtain ⟨v, hv⟩ := hsurj E
    have hz : v 0 = 0 := hunit.mul_right_eq_zero.mp (by
      rw [← cofactorCompletion_pairing Z w v, hv]
      exact hE)
    refine ⟨fun j => v j.succ, ?_⟩
    rw [← hv]
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cofactorCompletion, hz]
  · rintro ⟨c, rfl⟩
    rw [dotProduct_mulVec, ← Matrix.mulVec_transpose,
      rectangularCofactors_relation, zero_dotProduct]

theorem cofactor_kernel_bounded_eq_zero
    {K : Type*} [Field K]
    (Z : Matrix (Fin (N + 1)) (Fin N) K[X]) (w : Fin (N + 1) → K[X])
    (hunit : IsUnit (cofactorCompletion Z w).det)
    (e : Fin N → ℕ) (d : ℕ) (hd : ∀ j, d < e j)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (E : Fin (N + 1) → K[X]) (hE : ∀ i, (E i).natDegree ≤ d)
    (hrel : rectangularCofactors Z ⬝ᵥ E = 0) : E = 0 := by
  obtain ⟨c, hc⟩ := (cofactor_kernel_iff_range_of_completion_unit Z w hunit E).mp hrel
  have hb := (polynomial_combination_degree_iff Z e c d hZ hlead).mp
    (by simpa only [← hc] using hE)
  have hz : c = 0 := by
    funext j
    rcases hb j with hj | ⟨hj, _⟩
    · exact hj
    · exact False.elim ((Nat.not_le_of_lt (hd j)) hj)
  rw [hc, hz, Matrix.mulVec_zero]

theorem bounded_relation_eq_zero_of_scaled_cofactors
    {K : Type*} [Field K]
    (Z : Matrix (Fin (N + 1)) (Fin N) K[X])
    (F w : Fin (N + 1) → K[X]) (κ δ : K) (hκ : κ ≠ 0) (hδ : δ ≠ 0)
    (hcof : rectangularCofactors Z = C κ • F) (hbez : F ⬝ᵥ w = C δ)
    (e : Fin N → ℕ) (d : ℕ) (hd : ∀ j, d < e j)
    (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (E : Fin (N + 1) → K[X]) (hE : ∀ i, (E i).natDegree ≤ d)
    (hrel : F ⬝ᵥ E = 0) : E = 0 := by
  have hdet : (cofactorCompletion Z w).det = C (κ * δ) := by
    rw [cofactorCompletion_det]
    change w ⬝ᵥ rectangularCofactors Z = _
    rw [dotProduct_comm, hcof, smul_dotProduct, hbez]
    exact (map_mul C κ δ).symm
  have hu : IsUnit (cofactorCompletion Z w).det := by
    rw [hdet]
    exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hκ hδ)).map C
  apply cofactor_kernel_bounded_eq_zero Z w hu e d hd hZ hlead E hE
  rw [hcof, smul_dotProduct, hrel, smul_zero]

end FD56
