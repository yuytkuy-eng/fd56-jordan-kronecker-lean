/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MinimalProfile
import FD56.LinearAlgebra.MixedKernelPairings
import FD56.LinearAlgebra.MixedKroneckerBasis

/-! Actual reduced kernel bases with arbitrary degree lists give simultaneous
constant congruences when their Kronecker dimensions exhaust the ambient space. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

/-- The independent coefficient and pairing spaces of an actual reduced basis
provide the full mixed-chain congruence. -/
theorem mixed_reduced_kernel_basis_constant_congruence {r : ℕ}
    (A B : Matrix n n K)
    (basis : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : Fin r → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j))))
    (hcard : Fintype.card n = ∑ j, (2*d j+1))
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ G : Matrix n ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) K,
    ∃ J : Matrix ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) n K,
      G * J = 1 ∧ J * G = 1 ∧
      G.transpose * A * G =
        Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0 ∧
      G.transpose * B * G =
        Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0 := by
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  have hAV : affineMatrixPencil A B * V = 0 := polynomialKernelBasisMatrix_mul _ basis
  have hW : Function.Injective (mixedKernelCoefficientMatrix V d).mulVec :=
    mixed_kernel_basis_coefficients_injective A B basis d hdegree hlead
  have hL := mixed_kernel_basis_pairing_surjective A B basis d hA hdegree hlead
  have hLW := mixed_kernel_pairing_annihilates_coefficients d A B V hA hB hAV
  obtain ⟨hWA, hWB⟩ := mixed_kernel_pairing_identities d A B V hA hB hAV hdegree
  exact exists_mixed_kronecker_basis d A B (mixedKernelCoefficientMatrix V d)
    (mixedKernelPairingMatrix A V d) hcard hW hL hLW hWA hWB hA hB hAltA hAltB

/-- A prescribed actual minimal-degree multiset and the full dimension budget
imply an invertible simultaneous congruence, with the realized degrees retained
up to their exact list permutation. -/
theorem mixed_minimal_degrees_constant_congruence
    (A B : Matrix n n K) (xs : List ℕ)
    (hmin : HasMinimalKernelDegrees (affineMatrixPencil A B) xs)
    (hcard : Fintype.card n = (xs.map (fun e => 2*e+1)).sum)
    (hA : A.transpose = -A) (hB : B.transpose = -B)
    (hAltA : ∀ x : n → K, x ⬝ᵥ (A *ᵥ x) = 0)
    (hAltB : ∀ x : n → K, x ⬝ᵥ (B *ᵥ x) = 0) :
    ∃ (r : ℕ) (d : Fin r → ℕ), (List.ofFn d).Perm xs ∧
    ∃ G : Matrix n ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) K,
    ∃ J : Matrix ((Σ j, Fin (d j+1)) ⊕ (Σ j, Fin (d j))) n K,
      G * J = 1 ∧ J * G = 1 ∧
      G.transpose * A * G =
        Matrix.fromBlocks 0 (mixedCrossFirst d) (-(mixedCrossFirst d).transpose) 0 ∧
      G.transpose * B * G =
        Matrix.fromBlocks 0 (mixedCrossSecond d) (-(mixedCrossSecond d).transpose) 0 := by
  obtain ⟨r, basis, d, hdegree, hlead, hperm⟩ := hmin
  have hsum : (xs.map (fun e => 2*e+1)).sum = ∑ j, (2*d j+1) := by
    have h := (hperm.map (fun e => 2*e+1)).sum_eq
    simpa only [List.map_ofFn, List.sum_ofFn, Function.comp_apply] using h.symm
  refine ⟨r, d, hperm, ?_⟩
  exact mixed_reduced_kernel_basis_constant_congruence A B basis d hdegree hlead
    (hcard.trans hsum) hA hB hAltA hAltB

end FD56
