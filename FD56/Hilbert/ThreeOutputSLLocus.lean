/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.ThreeOutputOneSL
import FD56.Hilbert.ThreeOutputTwoSL
import FD56.Hilbert.GenericKroneckerLocus

/-! The exact three-output SL block lists hold on nonempty principal loci
in the original affine-pair coordinates, at every nondivisible depth. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K] [CharZero K]

theorem generic_three_one_sl_nonempty_principal_locus
    (q : ℕ) (i₀ : Fin (3*q+1)) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin (3*q+1)) (Fin 3) ⊕
      MatrixParameters (Fin (3*q+1)) (Fin 3)) K,
      δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
      ∀ x, MvPolynomial.eval x δ≠0 →
        HasKroneckerDecomposition (slKirillovMatrix
          ((universalAffineSquare K (Fin (3*q+1)) (Fin 3)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K (Fin (3*q+1)) (Fin 3)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))) i₀)
          (List.replicate 3 (threeOneFrameDegree q)) :=
  generic_sl_kronecker_nonempty_principal_locus i₀ _
    (generic_three_one_sl_minimal_and_kronecker q i₀).2

theorem generic_three_two_sl_nonempty_principal_locus
    (q : ℕ) (i₀ : Fin (3*q+2)) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin (3*q+2)) (Fin 3) ⊕
      MatrixParameters (Fin (3*q+2)) (Fin 3)) K,
      δ≠0 ∧ (∃ x, MvPolynomial.eval x δ≠0) ∧
      ∀ x, MvPolynomial.eval x δ≠0 →
        HasKroneckerDecomposition (slKirillovMatrix
          ((universalAffineSquare K (Fin (3*q+2)) (Fin 3)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K (Fin (3*q+2)) (Fin 3)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))) i₀)
          (List.replicate 3 (threeTwoFrameDegree q)) :=
  generic_sl_kronecker_nonempty_principal_locus i₀ _
    (generic_three_two_sl_minimal_and_kronecker q i₀).2

end FD56
