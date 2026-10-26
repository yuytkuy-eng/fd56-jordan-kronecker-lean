/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.GenericRowRatio
import FD56.LinearAlgebra.SplittingMatrixDiagonalization

/-! A generic square row pencil has an invertible leading matrix and a simple
eigenbasis after an explicitly injective coefficient extension. -/

noncomputable section
namespace FD56
open Matrix Polynomial

private theorem map_neg_mul_matrix {R E n : Type*} [CommRing R] [CommRing E]
    [Fintype n] [DecidableEq n] (phi : R →+* E) (A B : Matrix n n R) :
    (-A*B).map phi = -(A.map phi)*B.map phi := by
  change phi.mapMatrix (-A*B) = -phi.mapMatrix A * phi.mapMatrix B
  rw [map_mul,map_neg]

private theorem row_ratio_diagonalization {F E n : Type*} [Field F] [Field E]
    [Fintype n] [DecidableEq n] (tau : F →+* E) (A : Matrix n n F) (hunit : IsUnit A.det)
    (B P₀ P₁ S : Matrix n n E) (lam : n → E)
    (h₀ : P₀ = -(A.map tau)*B) (h₁ : P₁ = A.map tau)
    (hdiag : B*S = S*Matrix.diagonal lam) :
    ∃ V : Matrix n n E, P₁*V=1 ∧ V*P₁=1 ∧ (-V*P₀)*S = S*Matrix.diagonal lam := by
  let V := (A⁻¹).map tau
  have hAV : A.map tau * V = 1 := by
    change tau.mapMatrix A * tau.mapMatrix A⁻¹ = 1
    rw [← map_mul,Matrix.mul_nonsing_inv _ hunit,map_one]
  have hVA : V * A.map tau = 1 := by
    change tau.mapMatrix A⁻¹ * tau.mapMatrix A = 1
    rw [← map_mul,Matrix.nonsing_inv_mul _ hunit,map_one]
  refine ⟨V,?_,?_,?_⟩
  · rwa [h₁]
  · rwa [h₁]
  · rw [h₀,← Matrix.mul_assoc,neg_mul_neg,hVA,Matrix.one_mul]
    exact hdiag

variable (K n : Type*) [Field K] [Fintype n] [DecidableEq n]

abbrev GenericSquareRowField := (genericRowRatioMatrix K n).charpoly.SplittingField

def genericSquareRowEmbedding :
    MvPolynomial ((n × n) ⊕ (n × n)) K →+* GenericSquareRowField K n :=
  (algebraMap (GenericRowRatioField K n) (GenericSquareRowField K n)).comp
    (genericRowRatioEmbedding K n)

theorem genericSquareRowEmbedding_injective : Function.Injective (genericSquareRowEmbedding K n) := by
  intro x y h
  apply genericRowRatioEmbedding_injective K n
  exact (algebraMap (GenericRowRatioField K n) (GenericSquareRowField K n)).injective h

theorem generic_square_row_diagonalization :
    ∃ V S T : Matrix n n (GenericSquareRowField K n),
    ∃ lam : n → GenericSquareRowField K n,
      Function.Injective lam ∧ S*T=1 ∧ T*S=1 ∧
      (Matrix.of fun i j => genericSquareRowEmbedding K n (MvPolynomial.X (.inr (i,j))))*V=1 ∧
      V*(Matrix.of fun i j => genericSquareRowEmbedding K n (MvPolynomial.X (.inr (i,j))))=1 ∧
      (-V*(Matrix.of fun i j => genericSquareRowEmbedding K n (MvPolynomial.X (.inl (i,j)))))*S =
        S*Matrix.diagonal lam := by
  let rho : GenericRowRatioField K n →+* GenericSquareRowField K n := algebraMap _ _
  let kappa : GenericRowLeadingField K n →+* GenericRowRatioField K n :=
    (algebraMap (MvPolynomial (n × n) (GenericRowLeadingField K n))
      (GenericRowRatioField K n)).comp MvPolynomial.C
  let tau := rho.comp kappa
  let A := genericRowLeadingMatrix K n
  let B := (genericRowRatioMatrix K n).map rho
  have hunit : IsUnit A.det := isUnit_iff_ne_zero.mpr (genericRowLeadingMatrix_det_ne_zero K n)
  have hlead : (fun i j => genericSquareRowEmbedding K n (MvPolynomial.X (.inr (i,j)))) =
      A.map tau := by
    have h := congrArg (fun M : Matrix n n (GenericRowRatioField K n) => M.map rho)
      (genericRowRatioEmbedding_leading K n)
    exact h
  have hconstant : (fun i j => genericSquareRowEmbedding K n (MvPolynomial.X (.inl (i,j)))) =
      -(A.map tau)*B := by
    have h := congrArg (fun M : Matrix n n (GenericRowRatioField K n) => M.map rho)
      (genericRowRatioEmbedding_constant K n)
    exact h.trans (map_neg_mul_matrix rho (genericRowLeadingInRatio K n) (genericRowRatioMatrix K n))
  obtain ⟨S,T,lam,hlam,hST,hTS,hdiag⟩ := exists_splitting_field_diagonalization
    (genericRowRatioMatrix K n) (genericRowRatioMatrix_separable K n)
  obtain ⟨V,hP₁V,hVP₁,hfinal⟩ := row_ratio_diagonalization tau A hunit B _ _ S lam
    hconstant hlead hdiag
  exact ⟨V,S,T,lam,hlam,hST,hTS,hP₁V,hVP₁,hfinal⟩

end FD56
