/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericPencil
import FD56.LinearAlgebra.PolynomialLeading

/-! The linear coefficients of the generic affine pencil form a generic pair.
Thus the two observability ranks at the point at infinity are established. -/

noncomputable section
namespace FD56
open Matrix Polynomial

def affineLeadingParameterMap (K σ : Type*) [Field K] :
    MvPolynomial σ K →+* AffineCoefficientField K σ :=
  (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)).comp
    (MvPolynomial.rename (Sum.inr : σ → σ ⊕ σ)).toRingHom

theorem affineLeadingParameterMap_injective (K σ : Type*) [Field K] :
    Function.Injective (affineLeadingParameterMap K σ) :=
  (IsFractionRing.injective (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)).comp
    (MvPolynomial.rename_injective (R := K) (Sum.inr : σ → σ ⊕ σ) Sum.inr_injective)

theorem genericAffine_leading_pair (K n m : Type*) [Field K] :
    matrixCoeff (genericAffineSquare K n m) 1 =
      (universalSquare K n m).map (affineLeadingParameterMap K (MatrixParameters n m)) ∧
    matrixCoeff (genericAffineRows K n m) 1 =
      (universalRows K n m).map (affineLeadingParameterMap K (MatrixParameters n m)) := by
  constructor <;> funext i j <;>
    simp [matrixCoeff, genericAffineSquare, genericAffineRows, universalSquare, universalRows,
      affineParameterMap, affineLeadingParameterMap]

theorem generic_leading_observability {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] (q : ℕ) :
    let M := matrixCoeff (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) 1
    let P := matrixCoeff (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) 1
    Module.finrank (AffineCoefficientField K (MatrixParameters (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)))
      (unobservableSpace M P (q + 1)) = Fintype.card r ∧
    Module.finrank (AffineCoefficientField K (MatrixParameters (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)))
      (unobservableSpace M P (q + 2)) = 0 := by
  classical
  dsimp only
  obtain ⟨M₀, P₀, hf, hn⟩ := exists_regular_observability_pair (K := K) (r := r) (s := s) q
  have he := genericAffine_leading_pair K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)
  rw [he.1, he.2]
  exact universal_observability_profile (affineLeadingParameterMap K _)
    (affineLeadingParameterMap_injective K _) M₀ P₀ q (Fintype.card r)
    (blockIndex_card (m := r ⊕ s) (r := r) (q + 1)) hf hn

theorem generic_leading_observability_rows {K : Type*} {r s : Type} [Field K]
    [Fintype r] [Fintype s] (q : ℕ) :
    let M := matrixCoeff (genericAffineSquare K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) 1
    let P := matrixCoeff (genericAffineRows K (blockIndex (r ⊕ s) r (q + 1)) (r ⊕ s)) 1
    Function.Injective (observabilityMatrix M P (q + 1)).transpose.mulVec := by
  classical
  dsimp only
  apply matrix_transpose_injective_of_surjective
  apply observabilityMatrix_surjective
  apply observabilityMap_surjective_of_finrank
  rw [(generic_leading_observability (K := K) (r := r) (s := s) q).1, blockIndex_card]
  omega

end FD56
