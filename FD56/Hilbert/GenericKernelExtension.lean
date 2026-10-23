/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.GenericKernelBound
import FD56.LinearAlgebra.RankSpecializationExtension

/-! Affine witnesses over a field extension bound generic bounded kernels
over the original coefficient field. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem polynomial_kernel_finrank_le_of_field_specialization
    {R K F a b : Type*} [CommRing R] [Field K] [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ψ : R →+* K) (φ : R →+* F) (hφ : Function.Injective φ)
    (A : Matrix a b R[X]) (d : ℕ)
    (hAψ : DegreeBound (A.map (Polynomial.mapRingHom ψ)) 1)
    (hAφ : DegreeBound (A.map (Polynomial.mapRingHom φ)) 1) :
    Module.finrank F (polynomialKernelAtDegree (A.map (Polynomial.mapRingHom φ)) d) ≤
      Module.finrank K (polynomialKernelAtDegree (A.map (Polynomial.mapRingHom ψ)) d) := by
  rw [← coefficient_kernel_finrank _ d hAφ, ← coefficient_kernel_finrank _ d hAψ,
    polynomialCoefficientMatrix_map, polynomialCoefficientMatrix_map]
  exact matrix_kernel_finrank_le_of_field_specialization ψ φ hφ
    (polynomialCoefficientMatrix A d)

variable {K L n m : Type*} [Field K] [Field L]

def affinePairFieldSpecialization (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X]) :
    MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K →+* L :=
  MvPolynomial.eval₂Hom σ
    (Sum.elim
      (Sum.elim (fun ij => (M ij.1 ij.2).coeff 0) (fun ij => (P ij.1 ij.2).coeff 0))
      (Sum.elim (fun ij => (M ij.1 ij.2).coeff 1) (fun ij => (P ij.1 ij.2).coeff 1)))

theorem universalAffineSquare_field_specialization (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X]) (hM : DegreeBound M 1) :
    (universalAffineSquare K n m).map
      (Polynomial.mapRingHom (affinePairFieldSpecialization σ M P)) = M := by
  calc
    _ = affineMatrixPencil (fun i j => (M i j).coeff 0) (fun i j => (M i j).coeff 1) := by
      funext i j
      simp [universalAffineSquare, affineMatrixPencil, affinePairFieldSpecialization]
    _ = M := affineMatrixPencil_coefficients M hM

theorem universalAffineRows_field_specialization (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X]) (hP : DegreeBound P 1) :
    (universalAffineRows K n m).map
      (Polynomial.mapRingHom (affinePairFieldSpecialization σ M P)) = P := by
  calc
    _ = affineMatrixPencil (fun i j => (P i j).coeff 0) (fun i j => (P i j).coeff 1) := by
      funext i j
      simp [universalAffineRows, affineMatrixPencil, affinePairFieldSpecialization]
    _ = P := affineMatrixPencil_coefficients P hP

variable [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem generic_slHilbert_le_field_witness (σ : K →+* L)
    (M : Matrix n n L[X]) (P : Matrix m n L[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤
      slHilbert M P d := by
  let ψ := affinePairFieldSpecialization σ M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := slEquationMatrix (universalAffineSquare K n m) (universalAffineRows K n m) i₀
  have he : A.map (Polynomial.mapRingHom ψ) = slEquationMatrix M P i₀ := by
    dsimp only [A, ψ]
    rw [slEquationMatrix_map, universalAffineSquare_field_specialization σ M P hM,
      universalAffineRows_field_specialization σ M P hP]
  have hg : A.map (Polynomial.mapRingHom φ) =
      slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀ := by
    dsimp only [A, φ]
    rw [slEquationMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  have hs := polynomial_kernel_finrank_le_of_field_specialization ψ φ
    (IsFractionRing.injective _ _) A d
    (by rw [he]; exact slEquationMatrix_degree M P i₀ hM hP)
    (by
      rw [hg]
      exact slEquationMatrix_degree _ _ i₀
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m))
  rw [slHilbert_eq_matrix_kernel _ _ i₀ d, slHilbert_eq_matrix_kernel _ _ i₀ d]
  rw [he, hg] at hs
  exact hs

end FD56
