/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.PolynomialKernelCompletion

/-! Complementary minors of inverse matrices and primitive dual polynomial
bases, with the permutation sign kept explicit. No selected minor is assumed invertible. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {R a k : Type*} [CommRing R] [Fintype a] [Fintype k]
  [DecidableEq a] [DecidableEq k]

theorem inverse_block_complementary_det (J K : Matrix (a ⊕ k) (a ⊕ k) R)
    (hJK : J*K=1) : J.toBlocks₁₁.det=J.det*K.toBlocks₂₂.det := by
  have hblocks := hJK
  rw [← Matrix.fromBlocks_toBlocks J,← Matrix.fromBlocks_toBlocks K,
    Matrix.fromBlocks_multiply] at hblocks
  have h11 : J.toBlocks₁₁*K.toBlocks₁₁+J.toBlocks₁₂*K.toBlocks₂₁=1 := by
    have h := congrArg Matrix.toBlocks₁₁ hblocks
    simpa [Matrix.toBlocks₁₁,Matrix.one_apply] using h
  have h12 : J.toBlocks₁₁*K.toBlocks₁₂+J.toBlocks₁₂*K.toBlocks₂₂=0 := by
    have h := congrArg Matrix.toBlocks₁₂ hblocks
    simpa [Matrix.toBlocks₁₂,Matrix.one_apply] using h
  let M := Matrix.fromBlocks J.toBlocks₁₁ J.toBlocks₁₂
    (0 : Matrix k a R) (1 : Matrix k k R)
  have hMK : M*K=Matrix.fromBlocks (1 : Matrix a a R) 0 K.toBlocks₂₁ K.toBlocks₂₂ := by
    dsimp only [M]
    conv_lhs => rw [← Matrix.fromBlocks_toBlocks K]
    rw [Matrix.fromBlocks_multiply,h11,h12]
    simp only [Matrix.zero_mul,Matrix.one_mul,zero_add]
  have hd : J.toBlocks₁₁.det*K.det=K.toBlocks₂₂.det := by
    have h := congrArg Matrix.det hMK
    simpa only [Matrix.det_mul,M,Matrix.det_fromBlocks_zero₂₁,
      Matrix.det_fromBlocks_zero₁₂,Matrix.det_one,mul_one,one_mul] using h
  have hi : J.det*K.det=1 := by rw [← Matrix.det_mul,hJK,Matrix.det_one]
  calc
    J.toBlocks₁₁.det = J.toBlocks₁₁.det*(J.det*K.det) := by rw [hi,mul_one]
    _ = J.det*(J.toBlocks₁₁.det*K.det) := by rw [← mul_assoc,mul_comm J.toBlocks₁₁.det,mul_assoc]
    _ = _ := by rw [hd]

theorem inverse_block_permuted_complementary_det
    (J K : Matrix (a ⊕ k) (a ⊕ k) R) (hJK : J*K=1)
    (σ : Equiv.Perm (a ⊕ k)) :
    (J.submatrix (fun i => σ (Sum.inl i)) Sum.inl).det=
      ((Equiv.Perm.sign σ : ℤ) : R)*J.det*
        (K.submatrix Sum.inr (fun i => σ (Sum.inr i))).det := by
  have h : J.submatrix σ id*K.submatrix id σ=1 := by
    rw [← Matrix.submatrix_mul J K σ id σ Function.bijective_id,hJK]
    exact Matrix.submatrix_one_equiv σ
  have hd := inverse_block_complementary_det (J.submatrix σ id) (K.submatrix id σ) h
  rw [Matrix.det_permute] at hd
  exact hd

theorem inverse_pair_column_minors_complement
    (G : Matrix (a ⊕ k) a R) (Q : Matrix (a ⊕ k) k R)
    (L : Matrix a (a ⊕ k) R) (T : Matrix (a ⊕ k) k R)
    (h : Matrix.fromCols G Q*Matrix.fromRows L T.transpose=1)
    (σ : Equiv.Perm (a ⊕ k)) :
    (G.submatrix (fun i => σ (Sum.inl i)) id).det=
      ((Equiv.Perm.sign σ : ℤ) : R)*(Matrix.fromCols G Q).det*
        (T.submatrix (fun i => σ (Sum.inr i)) id).det := by
  have hd := inverse_block_permuted_complementary_det
    (Matrix.fromCols G Q) (Matrix.fromRows L T.transpose) h σ
  change (G.submatrix (fun i => σ (Sum.inl i)) id).det=_ at hd
  have he : (Matrix.fromRows L T.transpose).submatrix Sum.inr
      (fun i => σ (Sum.inr i))=(T.submatrix (fun i => σ (Sum.inr i)) id).transpose := rfl
  rw [he,Matrix.det_transpose] at hd
  exact hd

theorem polynomial_dual_basis_complementary_minors {F : Type*} [Field F]
    (G : Matrix (a ⊕ k) a F[X]) (L : Matrix a (a ⊕ k) F[X]) (hLG : L*G=1)
    (B : Basis k F[X] (LinearMap.ker (Matrix.toLin' G.transpose))) :
    ∃ c : F, c≠0 ∧ ∀ σ : Equiv.Perm (a ⊕ k),
      (G.submatrix (fun i => σ (Sum.inl i)) id).det=
        ((Equiv.Perm.sign σ : ℤ) : F[X])*C c*
          ((polynomialKernelBasisMatrix G.transpose B).submatrix
            (fun i => σ (Sum.inr i)) id).det := by
  have hGL : G.transpose*L.transpose=1 := by
    rw [← Matrix.transpose_mul,hLG,Matrix.transpose_one]
  obtain ⟨S,_,_,_,_,hHJ⟩ := polynomial_kernel_basis_completion G.transpose L.transpose hGL B
  have h : Matrix.fromCols G S.transpose*
      Matrix.fromRows L (polynomialKernelBasisMatrix G.transpose B).transpose=1 := by
    simpa only [Matrix.transpose_mul,Matrix.transpose_fromRows,Matrix.transpose_fromCols,
      Matrix.transpose_transpose,Matrix.transpose_one] using congrArg Matrix.transpose hHJ
  have hd : (Matrix.fromCols G S.transpose).det*
      (Matrix.fromRows L (polynomialKernelBasisMatrix G.transpose B).transpose).det=1 := by
    rw [← Matrix.det_mul,h,Matrix.det_one]
  have hu : IsUnit (Matrix.fromCols G S.transpose).det :=
    isUnit_iff_dvd_one.mpr ⟨_,hd.symm⟩
  obtain ⟨c,hc,he⟩ := Polynomial.isUnit_iff.mp hu
  refine ⟨c,hc.ne_zero,?_⟩
  intro σ
  have hm := inverse_pair_column_minors_complement G S.transpose L
    (polynomialKernelBasisMatrix G.transpose B) h σ
  rw [← he] at hm
  exact hm

end FD56
