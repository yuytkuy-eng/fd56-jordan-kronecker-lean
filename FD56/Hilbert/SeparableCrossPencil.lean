/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.AffineCrossNormalization
import FD56.LinearAlgebra.AffineRatioSeparable

/-! A separable cross determinant gives a full constant decomposition into simple regular blocks. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {K n : Type*} [Field K] [Fintype n] [DecidableEq n]

theorem alternatingCrossPencil_map {L : Type*} [Field L] (φ : K →+* L)
    (A B P₀ P₁ : Matrix n n K) :
    (alternatingCrossPencil A B P₀ P₁).map (Polynomial.mapRingHom φ) =
      alternatingCrossPencil (A.map φ) (B.map φ) (P₀.map φ) (P₁.map φ) := by
  funext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [alternatingCrossPencil, affineMatrixPencil, Matrix.map_apply]

theorem alternatingCrossPencil_separable_jordan_decomposition
    (A B P₀ P₁ : Matrix n n K)
    (hA : ∀ v, v ⬝ᵥ (A *ᵥ v)=0) (hB : ∀ v, v ⬝ᵥ (B *ᵥ v)=0)
    (hP₁ : P₁.det ≠ 0) (hsep : (affineMatrixPencil P₀ P₁).det.Separable) :
    let L := (-P₁⁻¹*P₀).charpoly.SplittingField
    ∃ lam : n → L, Function.Injective lam ∧
    ∃ Q : Matrix (n ⊕ n) ((Fin 1 ⊕ Fin 1) × n) L,
    ∃ R : Matrix ((Fin 1 ⊕ Fin 1) × n) (n ⊕ n) L,
      Q*R=1 ∧ R*Q=1 ∧
      (Q.map C).transpose *
        (alternatingCrossPencil A B P₀ P₁).map (Polynomial.mapRingHom (algebraMap K L)) *
        Q.map C = Matrix.blockDiagonal (fun i => skewJordanBlockPencil (lam i) 1) := by
  intro L
  let φ : K →+* L := algebraMap K L
  have hP₁V : P₁*P₁⁻¹=1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hP₁)
  have hVP₁ : P₁⁻¹*P₁=1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hP₁)
  have hs : (-P₁⁻¹*P₀).charpoly.Separable := affine_ratio_charpoly_separable P₀ P₁ _ hVP₁ hsep
  obtain ⟨S,T,lam,hlam,hST,hTS,hdiag⟩ := exists_splitting_field_diagonalization (-P₁⁻¹*P₀) hs
  have hP₁V' : P₁.map φ * (P₁⁻¹).map φ=1 := by
    rw [← Matrix.map_mul, hP₁V, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have hVP₁' : (P₁⁻¹).map φ * P₁.map φ=1 := by
    rw [← Matrix.map_mul, hVP₁, Matrix.map_one _ (map_zero φ) (map_one φ)]
  have he : (-P₁⁻¹*P₀).map φ = -(P₁⁻¹).map φ * P₀.map φ := by
    rw [Matrix.map_mul]
    congr 1
    funext i j
    exact map_neg φ _
  change ((-P₁⁻¹*P₀).map φ)*S=S*Matrix.diagonal lam at hdiag
  rw [he] at hdiag
  obtain ⟨Q,R,hQR,hRQ,hcong⟩ := alternatingCrossPencil_simple_jordan_of_eigenbasis
    (A.map φ) (B.map φ) (P₀.map φ) (P₁.map φ) ((P₁⁻¹).map φ) S T
    hST hTS hP₁V' hVP₁' (matrix_alternating_map φ A hA) (matrix_alternating_map φ B hB)
    lam hlam hdiag
  refine ⟨lam,hlam,Q,R,hQR,hRQ,?_⟩
  rw [alternatingCrossPencil_map]
  exact hcong

end FD56
