/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalBasis
import FD56.Hilbert.MinimalIndices

/-! A Hilbert profile is equivalent to the existence of an actual reduced
polynomial kernel basis with the prescribed degree multiset. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

def HasMinimalKernelDegrees (A : Matrix a b K[X]) (xs : List ℕ) : Prop :=
  ∃ (r : ℕ) (B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' A)))
    (e : Fin r → ℕ),
    (∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j) ∧
    Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (e j))) ∧
    (List.ofFn e).Perm xs

theorem hasMinimalKernelDegrees_iff_hilbert (A : Matrix a b K[X]) (xs : List ℕ) :
    HasMinimalKernelDegrees A xs ↔
      ∀ d : ℕ, Module.finrank K (polynomialKernelAtDegree A d) =
        (xs.map (fun e => d + 1 - e)).sum := by
  constructor
  · rintro ⟨r, B, e, hZ, hlead, hperm⟩ d
    rw [polynomial_kernel_basis_hilbert A B e d hZ hlead]
    have hh := (hperm.map (fun e => d + 1 - e)).sum_eq
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using hh
  · intro hh
    obtain ⟨r, B, e, hZ, hlead, _, hB⟩ := polynomial_kernel_has_minimal_basis A
    refine ⟨r, B, e, hZ, hlead, ?_⟩
    apply listHilbert_determines_indices
    intro d
    rw [listHilbert_ofFn, listHilbert_nat]
    exact_mod_cast (hB d).symm.trans (hh d)

end FD56
