/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.IndependentSquareSLDecomposition
import FD56.Stabilizer.GenericSquareGLClassification
import FD56.Hilbert.MixedSLKronecker

/-! The actual generic square SL pencil has a separated singular and regular
decomposition over the same explicit coefficient extension as square GL. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem slKirillovMatrix_map {R E n m : Type*} [CommRing R] [CommRing E]
    [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]
    (phi : R →+* E) (M : Matrix n n R) (P : Matrix m n R) (i₀ : n) :
    (slKirillovMatrix M P i₀).map phi = slKirillovMatrix (M.map phi) (P.map phi) i₀ := by
  simp only [slKirillovMatrix,Matrix.map_mul,Matrix.transpose_map,
    slChartEmbeddingMatrix_map,glKirillovMatrix_map]

variable {K : Type*} [Field K]

theorem generic_square_sl_scalar_kronecker_decomposition (i₀ : Fin 1) :
    HasKroneckerDecomposition (slKirillovMatrix (genericAffineSquare K (Fin 1) (Fin 1))
      (genericAffineRows K (Fin 1) (Fin 1)) i₀) [0] := by
  have hi : i₀=0 := Subsingleton.elim _ _
  subst i₀
  apply slKirillovMatrix_kronecker _ _ 0 [0]
    (genericAffineSquare_degree K _ _) (genericAffineRows_degree K _ _)
  · simpa using generic_square_sl_minimal_degrees (K := K) 1 (by decide)
  · simp [slChartInput_card,SLInput]

variable (K) (n : Type*) [Fintype n] [DecidableEq n] [Nontrivial n]

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem generic_square_sl_separated_decomposition (i₀ : n) :
    ∃ lam : n → GenericSquareGLSplittingField K n, Function.Injective lam ∧
    ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) (GenericSquareGLSplittingField K n),
    ∃ H : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) (GenericSquareGLSplittingField K n),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose *
          (slKirillovMatrix (genericAffineSquare K n n) (genericAffineRows K n n) i₀).map
            (Polynomial.mapRingHom (genericSquareGLFieldEmbedding K n)) * G.map C =
        squareSLSeparatedTarget lam j i₀ := by
  obtain ⟨V,S,T,lam,hlam,hST,hTS,hP₁V,hVP₁,hdiag⟩ := generic_square_row_diagonalization K n
  let phi : MvPolynomial ((n × n) ⊕ (n × n)) (GenericSquareRowField K n) →+*
      GenericSquareGLSplittingField K n := algebraMap _ _
  let kappa := phi.comp MvPolynomial.C
  refine ⟨fun i => kappa (lam i),kappa.injective.comp hlam,?_⟩
  simp_rw [slKirillovMatrix_map]
  change ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLChartInput n n i₀) (squareSLGroupedIndex j i₀) (GenericSquareGLSplittingField K n),
    ∃ H : Matrix (squareSLGroupedIndex j i₀) (SLChartInput n n i₀) (GenericSquareGLSplittingField K n),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose * slKirillovMatrix
        ((genericAffineSquare K n n).map (Polynomial.mapRingHom
          (squareGenericFieldMap (genericSquareRowEmbedding K n) (genericSquareRowEmbedding_injective K n))))
        ((genericAffineRows K n n).map (Polynomial.mapRingHom
          (squareGenericFieldMap (genericSquareRowEmbedding K n) (genericSquareRowEmbedding_injective K n))))
        i₀ * G.map C = squareSLSeparatedTarget (fun i => kappa (lam i)) j i₀
  simp_rw [squareGenericFieldMap_state_pencil,squareGenericFieldMap_row_pencil]
  exact independent_squareSL_separated_decomposition phi (IsFractionRing.injective _ _)
    (genericSquareRowConstant (genericSquareRowEmbedding K n))
    (genericSquareRowLeading (genericSquareRowEmbedding K n)) V S T hST hTS hP₁V hVP₁ lam hlam hdiag i₀

end FD56
