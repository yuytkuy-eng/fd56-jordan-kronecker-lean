/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.KroneckerSpecialization
import FD56.Hilbert.FiveTwoSLClassification

/-! Nonempty principal loci for the actual GL and SL pencils with a proved generic decomposition. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private theorem glKirillov_map_for_specialization {R S n m : Type*}
    [CommRing R] [CommRing S] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (φ : R →+* S)
    (M : Matrix n n R) (P : Matrix m n R) :
    (glKirillovMatrix M P).map φ = glKirillovMatrix (M.map φ) (P.map φ) := by
  simpa only [glKirillovMatrix,Matrix.submatrix_map] using
    congrArg (fun A => A.submatrix (glTraceDualIndexEquiv n m) id)
      (glEquationMatrix_map φ M P)

private theorem slKirillov_map_for_specialization {R S n m : Type*}
    [CommRing R] [CommRing S] [Fintype n] [Fintype m]
    [DecidableEq n] [DecidableEq m] (φ : R →+* S)
    (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (slKirillovMatrix M P i₀).map φ = slKirillovMatrix (M.map φ) (P.map φ) i₀ := by
  simp only [slKirillovMatrix,Matrix.map_mul,Matrix.transpose_map,
    slChartEmbeddingMatrix_map,glKirillov_map_for_specialization]

variable {K n m : Type*} [Field K] [Infinite K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_gl_kronecker_nonempty_principal_locus (xs : List ℕ)
    (h : HasKroneckerDecomposition
      (glKirillovMatrix (genericAffineSquare K n m) (genericAffineRows K n m)) xs) :
    ∃ δ : MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K,
      δ ≠ 0 ∧ (∃ x, MvPolynomial.eval x δ ≠ 0) ∧
      ∀ x, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (glKirillovMatrix
          ((universalAffineSquare K n m).map (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K n m).map (Polynomial.mapRingHom (MvPolynomial.eval x)))) xs := by
  have hg : HasKroneckerDecomposition
      ((glKirillovMatrix (universalAffineSquare K n m) (universalAffineRows K n m)).map
        (Polynomial.mapRingHom (algebraMap _ (AffineCoefficientField K (MatrixParameters n m))))) xs := by
    rw [glKirillov_map_for_specialization,universalAffineSquare_generic,universalAffineRows_generic]
    exact h
  obtain ⟨δ,hδ,hnon,he⟩ := kronecker_decomposition_nonempty_principal_locus _ xs hg
  refine ⟨δ,hδ,hnon,?_⟩
  intro x hx
  simpa only [glKirillov_map_for_specialization] using he x hx

theorem generic_sl_kronecker_nonempty_principal_locus (i₀ : n) (xs : List ℕ)
    (h : HasKroneckerDecomposition
      (slKirillovMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀) xs) :
    ∃ δ : MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K,
      δ ≠ 0 ∧ (∃ x, MvPolynomial.eval x δ ≠ 0) ∧
      ∀ x, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (slKirillovMatrix
          ((universalAffineSquare K n m).map (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K n m).map (Polynomial.mapRingHom (MvPolynomial.eval x))) i₀) xs := by
  have hg : HasKroneckerDecomposition
      ((slKirillovMatrix (universalAffineSquare K n m) (universalAffineRows K n m) i₀).map
        (Polynomial.mapRingHom (algebraMap _ (AffineCoefficientField K (MatrixParameters n m))))) xs := by
    rw [slKirillov_map_for_specialization,universalAffineSquare_generic,universalAffineRows_generic]
    exact h
  obtain ⟨δ,hδ,hnon,he⟩ := kronecker_decomposition_nonempty_principal_locus _ xs hg
  refine ⟨δ,hδ,hnon,?_⟩
  intro x hx
  simpa only [slKirillov_map_for_specialization] using he x hx

theorem generic_two_output_odd_sl_nonempty_principal_locus (q : ℕ) (i₀ : Fin (2*q+1)) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin (2*q+1)) (Fin 2) ⊕
        MatrixParameters (Fin (2*q+1)) (Fin 2)) K,
      δ ≠ 0 ∧ (∃ x, MvPolynomial.eval x δ ≠ 0) ∧
      ∀ x, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (slKirillovMatrix
          ((universalAffineSquare K (Fin (2*q+1)) (Fin 2)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K (Fin (2*q+1)) (Fin 2)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))) i₀) [q*(q+2),q*(q+2)] :=
  generic_sl_kronecker_nonempty_principal_locus i₀ [q*(q+2),q*(q+2)]
    (generic_two_output_odd_sl_all_depths q i₀)

theorem generic_five_two_sl_nonempty_principal_locus (i₀ : Fin 5) :
    ∃ δ : MvPolynomial (MatrixParameters (Fin 5) (Fin 2) ⊕
        MatrixParameters (Fin 5) (Fin 2)) K,
      δ ≠ 0 ∧ (∃ x, MvPolynomial.eval x δ ≠ 0) ∧
      ∀ x, MvPolynomial.eval x δ ≠ 0 →
        HasKroneckerDecomposition (slKirillovMatrix
          ((universalAffineSquare K (Fin 5) (Fin 2)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x)))
          ((universalAffineRows K (Fin 5) (Fin 2)).map
            (Polynomial.mapRingHom (MvPolynomial.eval x))) i₀) [8,8] :=
  generic_sl_kronecker_nonempty_principal_locus i₀ [8,8]
    (generic_five_two_sl_kronecker_decomposition i₀)

end FD56
