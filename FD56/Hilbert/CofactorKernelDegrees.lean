/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CofactorKernelComplement
import FD56.LinearAlgebra.ExactKernelBasis
import FD56.Hilbert.MinimalProfile

/-! A reduced cofactor certificate determines every bounded relation dimension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K : Type*} [Field K] {N : ℕ}

theorem scaled_cofactor_row_minimal_degrees
    (Z : Matrix (Fin (N + 1)) (Fin N) K[X])
    (F w : Fin (N + 1) → K[X]) (κ δ : K) (hκ : κ ≠ 0) (hδ : δ ≠ 0)
    (hcof : rectangularCofactors Z = C κ • F) (hbez : F ⬝ᵥ w = C δ)
    (e : Fin N → ℕ) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j)))) :
    HasMinimalKernelDegrees (fun _ : Unit => F) (List.ofFn e) := by
  have hdet : (cofactorCompletion Z w).det = C (κ * δ) := by
    rw [cofactorCompletion_det]
    change w ⬝ᵥ rectangularCofactors Z = _
    rw [dotProduct_comm, hcof, smul_dotProduct, hbez]
    exact (map_mul C κ δ).symm
  have hu : IsUnit (cofactorCompletion Z w).det := by
    rw [hdet]
    exact (isUnit_iff_ne_zero.mpr (mul_ne_zero hκ hδ)).map C
  have hi := Matrix.mulVec_injective_of_isUnit
    ((Matrix.isUnit_iff_isUnit_det _).mpr hu)
  have hmul (v : Fin N → K[X]) :
      cofactorCompletion Z w *ᵥ Fin.cases 0 v = Z *ᵥ v := by
    funext i
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, cofactorCompletion]
  have hZi : Function.Injective Z.mulVec := by
    intro v u h
    have hc := hi ((hmul v).trans (h.trans (hmul u).symm))
    funext j
    exact congrFun hc j.succ
  have hex (x : Fin (N + 1) → K[X]) :
      (fun _ : Unit => F) *ᵥ x = 0 ↔ ∃! v : Fin N → K[X], x = Z *ᵥ v := by
    have hrow : (fun _ : Unit => F) *ᵥ x = 0 ↔ F ⬝ᵥ x = 0 := by
      constructor
      · intro h
        exact congrFun h ()
      · intro h
        funext i
        exact h
    have hscaled : rectangularCofactors Z ⬝ᵥ x = 0 ↔ F ⬝ᵥ x = 0 := by
      rw [hcof, smul_dotProduct]
      change C κ * (F ⬝ᵥ x) = 0 ↔ _
      simp only [mul_eq_zero, Polynomial.C_eq_zero, hκ, false_or]
    rw [hrow, ← hscaled, cofactor_kernel_iff_range_of_completion_unit Z w hu]
    constructor
    · rintro ⟨v, hv⟩
      exact ⟨v, hv, fun u hu => hZi (hu.symm.trans hv)⟩
    · rintro ⟨v, hv, _⟩
      exact ⟨v, hv⟩
  obtain ⟨B, hB⟩ := kernel_basis_of_unique_coordinates (fun _ : Unit => F) Z hex
  have he : polynomialKernelBasisMatrix (fun _ : Unit => F) B = Z :=
    funext fun i => funext fun j => hB i j
  refine ⟨N, B, e, ?_, ?_, List.Perm.refl _⟩
  · rw [he]
    exact hZ
  · rw [he]
    exact hlead

theorem scaled_cofactor_row_kernel_hilbert
    (Z : Matrix (Fin (N + 1)) (Fin N) K[X])
    (F w : Fin (N + 1) → K[X]) (κ δ : K) (hκ : κ ≠ 0) (hδ : δ ≠ 0)
    (hcof : rectangularCofactors Z = C κ • F) (hbez : F ⬝ᵥ w = C δ)
    (e : Fin N → ℕ) (hZ : ∀ i j, (Z i j).natDegree ≤ e j)
    (hlead : Function.Injective (Matrix.mulVec (fun i j => (Z i j).coeff (e j))))
    (d : ℕ) :
    Module.finrank K (polynomialKernelAtDegree (fun _ : Unit => F) d) =
      ∑ j, (d + 1 - e j) := by
  have h := (hasMinimalKernelDegrees_iff_hilbert _ _).mp
    (scaled_cofactor_row_minimal_degrees Z F w κ δ hκ hδ hcof hbez e hZ hlead) d
  simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h

end FD56
