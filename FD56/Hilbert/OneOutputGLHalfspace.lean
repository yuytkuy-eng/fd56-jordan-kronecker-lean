/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.OneOutputSL
import FD56.Hilbert.SingleBlockIsotropy
import FD56.Hilbert.IsotropicBlockForm

/-! The generic one-output GL pencil has a constant isotropic halfspace. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K : Type*} [Field K]

theorem generic_one_output_gl_isotropic_halfspace (N : ℕ) (hN : 0<N) :
    ∃ Q : Matrix (SLInput (Fin N) (Fin 1)) (Fin (N*(N+1)/2))
      (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1))),
      Function.Injective Q.mulVec ∧
      (Q.map C).transpose * glKirillovMatrix
        (genericAffineSquare K (Fin N) (Fin 1))
        (genericAffineRows K (Fin N) (Fin 1)) * Q.map C=0 := by
  let i₀ : Fin N := ⟨0,hN⟩
  have hD : 0<N*(N+1)/2 := by
    rw [← oneOutputWeight_eq]
    have hw := oneOutputWeight_twice N
    nlinarith
  have h := single_block_restriction_isotropic_columns
    (glKirillovMatrix (genericAffineSquare K (Fin N) (Fin 1))
      (genericAffineRows K (Fin N) (Fin 1)))
    (slChartEmbeddingMatrix i₀) (slChartRetractionMatrix i₀)
    (slChartRetractionMatrix_embedding i₀) (N*(N+1)/2-1)
    (by simpa only [slChartEmbeddingMatrix_map,slKirillovMatrix] using
      generic_one_output_sl_kronecker_decomposition (K := K) N hN i₀)
  have he : N*(N+1)/2-1+1=N*(N+1)/2 := by omega
  rw [he] at h
  exact h

theorem generic_one_output_gl_isotropic_block_form (N : ℕ) (hN : 0<N) :
    ∃ S : Matrix (SLInput (Fin N) (Fin 1)) (Fin (N*(N+1)/2) ⊕ Fin (N*(N+1)/2))
      (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1))),
    ∃ T : Matrix (Fin (N*(N+1)/2) ⊕ Fin (N*(N+1)/2)) (SLInput (Fin N) (Fin 1))
      (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1))),
    ∃ A W : Matrix (Fin (N*(N+1)/2)) (Fin (N*(N+1)/2))
      (AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1)))[X],
      S*T=1 ∧ T*S=1 ∧
      (S.map C).transpose * glKirillovMatrix
        (genericAffineSquare K (Fin N) (Fin 1))
        (genericAffineRows K (Fin N) (Fin 1)) * S.map C =
          Matrix.fromBlocks A W (-W.transpose) 0 ∧
      DegreeBound A 1 ∧ DegreeBound W 1 ∧
      ∀ k (v : Fin (N*(N+1)/2) → AffineCoefficientField K (MatrixParameters (Fin N) (Fin 1))),
        v ⬝ᵥ ((fun i j => (A i j).coeff k)*ᵥv)=0 := by
  obtain ⟨Q,hinj,hiso⟩ := generic_one_output_gl_isotropic_halfspace (K := K) N hN
  apply constant_isotropic_halfspace_block_form (N*(N+1)/2) _
    (glKirillovMatrix_degreeBound _ _ 1 (genericAffineSquare_degree _ _ _)
      (genericAffineRows_degree _ _ _))
    (glKirillovMatrix_skew _ _) (glKirillovMatrix_alternating _ _) Q hinj hiso
  simp only [SLInput,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,mul_one]
  rw [← oneOutputWeight_eq]
  nlinarith [oneOutputWeight_twice N]

end FD56
