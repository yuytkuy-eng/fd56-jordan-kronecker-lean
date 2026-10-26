/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericRowDiagonalization
import FD56.Stabilizer.GenericSquareGLJordan
import FD56.Stabilizer.SquareGLScalarJordan

/-! The full generic square GL Jordan decomposition over an injective coefficient
extension: one block of dimension four and n-2 blocks of dimension two per pole
for n at least two. The scalar case is covered by the imported theorem. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable (K n : Type*) [Field K] [Fintype n] [DecidableEq n]

abbrev GenericSquareGLSplittingField := SquareGLIndependentField (GenericSquareRowField K n) n

def genericSquareGLFieldEmbedding :
    AffineCoefficientField K (MatrixParameters n n) →+* GenericSquareGLSplittingField K n :=
  squareGenericFieldMap (genericSquareRowEmbedding K n) (genericSquareRowEmbedding_injective K n)

theorem genericSquareGLFieldEmbedding_injective : Function.Injective (genericSquareGLFieldEmbedding K n) :=
  (genericSquareGLFieldEmbedding K n).injective

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1000000 in
theorem generic_square_gl_jordan_decomposition [Nontrivial n] :
    ∃ lam : n → GenericSquareGLSplittingField K n, Function.Injective lam ∧
    ∃ j : n → n, (∀ i, i≠j i) ∧
    ∃ G : Matrix (SLInput n n) (squareGLJordanIndex j) (GenericSquareGLSplittingField K n),
    ∃ H : Matrix (squareGLJordanIndex j) (SLInput n n) (GenericSquareGLSplittingField K n),
      G*H=1 ∧ H*G=1 ∧
      (G.map C).transpose *
          (glKirillovMatrix (genericAffineSquare K n n) (genericAffineRows K n n)).map
            (Polynomial.mapRingHom (genericSquareGLFieldEmbedding K n)) * G.map C =
        squareGLJordanTarget lam j := by
  obtain ⟨V,S,T,lam,hlam,hST,hTS,hP₁V,hVP₁,hdiag⟩ := generic_square_row_diagonalization K n
  let kappa : GenericSquareRowField K n →+* GenericSquareGLSplittingField K n :=
    (algebraMap (MvPolynomial ((n × n) ⊕ (n × n)) (GenericSquareRowField K n))
      (GenericSquareGLSplittingField K n)).comp MvPolynomial.C
  refine ⟨fun i => kappa (lam i),kappa.injective.comp hlam,?_⟩
  exact generic_square_gl_jordan_of_row_diagonalization
    (genericSquareRowEmbedding K n) (genericSquareRowEmbedding_injective K n)
    V S T hST hTS hP₁V hVP₁ lam hlam hdiag

end FD56
