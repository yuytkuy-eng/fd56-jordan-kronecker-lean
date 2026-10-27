/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NilpotentRankTwoFixedDimension
import FD56.LinearAlgebra.PrimaryPencilCoordinates

/-! Literal local Jordan blocks for the actual restriction of an affine polynomial pencil. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem polynomial_primary_jordan_decomposition {K n i : Type*} [Field K]
    [Fintype n] [DecidableEq n] [Fintype i] [DecidableEq i]
    (H : Matrix n n K[X]) (hH : DegreeBound H 1)
    (hA : ∀ v, v ⬝ᵥ ((fun r s => (H r s).coeff 0) *ᵥ v)=0)
    (hB : ∀ v, v ⬝ᵥ ((fun r s => (H r s).coeff 1) *ᵥ v)=0)
    (hd : Matrix.det (fun r s => (H r s).coeff 1)≠0)
    (x : K) (m : ℕ) (hdim : Fintype.card i=2*m)
    (hr : Module.finrank K (LinearMap.range (primaryShift (polynomialPencilOperator H) x))=2)
    (b : Basis i K ((polynomialPencilOperator H).maxGenEigenspace x)) :
    ∃ T : Matrix i (rankTwoJordanIndex (m-2)) K,
    ∃ U : Matrix (rankTwoJordanIndex (m-2)) i K,
      T*U=1 ∧ U*T=1 ∧
      (((subspaceBasisColumns _ b)*T).map C).transpose*H*((subspaceBasisColumns _ b)*T).map C=
        rankTwoJordanPencil x (m-2) := by
  let A : Matrix n n K := fun r s => (H r s).coeff 0
  let B : Matrix n n K := fun r s => (H r s).coeff 1
  let f := polynomialPencilOperator H
  let G := BilinForm.toMatrix b (B.toBilin'.restrict (f.maxGenEigenspace x))
  let N := LinearMap.toMatrix b b (primaryShift f x)
  let Q := subspaceBasisColumns (f.maxGenEigenspace x) b
  obtain ⟨hnd,ha,hBf,hself⟩ := alternating_pencil_operator_forms A B hA hB hd
  obtain ⟨hGdet,hG,hGN,hn,hrN⟩ :=
    primary_matrix_pair_properties B.toBilin' f hnd ha hBf hself x b
  have hcoordinate : (Q.map C).transpose*H*Q.map C=(X-C x)•G.map C-(G*N).map C := by
    rw [← affineMatrixPencil_coefficients H hH]
    exact primary_affine_pencil_coordinates A B hd x b
  obtain ⟨_,T,U,hTU,hUT,hcong⟩ := nilpotent_rank_two_fixed_dimension_jordan m hdim
    G N x hG hGN hGdet hn (hrN.trans hr)
  refine ⟨T,U,hTU,hUT,?_⟩
  change ((Q*T).map C).transpose*H*(Q*T).map C=_
  rw [Matrix.map_mul,Matrix.transpose_mul]
  calc
    _ = (T.map C).transpose*((Q.map C).transpose*H*Q.map C)*T.map C := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hcoordinate,hcong]

end FD56
