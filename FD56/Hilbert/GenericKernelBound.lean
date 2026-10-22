/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.AffineSpecialization
import FD56.Hilbert.EquationDegree
import FD56.Hilbert.Coefficients

/-! Arbitrary kernel dimensions at an affine witness bound the corresponding
generic bounded kernels. The witness need not have maximal matrix rank. -/

noncomputable section
namespace FD56
open Matrix Polynomial

theorem matrix_kernel_finrank_le_of_specialization
    {R K F a b : Type*} [CommRing R] [Field K] [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ι : K →+* R) (ψ : R →+* K) (hι : ∀ c, ψ (ι c) = c)
    (φ : R →+* F) (hφ : Function.Injective φ) (A : Matrix a b R) :
    Module.finrank F (LinearMap.ker (Matrix.toLin' (A.map φ))) ≤
      Module.finrank K (LinearMap.ker (Matrix.toLin' (A.map ψ))) := by
  classical
  let W := LinearMap.ker (Matrix.toLin' (A.map ψ))
  let k := Module.finrank K W
  let B := Module.finBasis K W
  obtain ⟨π, hπ⟩ := W.subtype.exists_leftInverse_of_injective W.ker_subtype
  let Q : (b → K) →ₗ[K] (Fin k → K) := B.equivFun.toLinearMap.comp π
  let D : Matrix (Fin k) b K := LinearMap.toMatrix' Q
  have hD (v : b → K) : D *ᵥ v = B.equivFun (π v) := by
    change Matrix.toLin' (LinearMap.toMatrix' Q) v = _
    rw [Matrix.toLin'_toMatrix']
    rfl
  have haug : Function.Injective (Matrix.fromRows (A.map ψ) D).mulVec := by
    intro v w h
    have hA : A.map ψ *ᵥ v = A.map ψ *ᵥ w := by
      funext i
      exact congrFun h (Sum.inl i)
    have hQ : π v = π w := by
      apply B.equivFun.injective
      rw [← hD, ← hD]
      funext i
      exact congrFun h (Sum.inr i)
    have hu : v - w ∈ W := by
      change A.map ψ *ᵥ (v - w) = 0
      rw [Matrix.mulVec_sub, hA, sub_self]
    let u : W := ⟨v - w, hu⟩
    have hzero : u = 0 := by
      have hh := LinearMap.congr_fun hπ u
      change π (v - w) = u at hh
      rw [map_sub, hQ, sub_self] at hh
      exact hh.symm
    exact sub_eq_zero.mp (congrArg Subtype.val hzero)
  have haugR : Function.Injective
      ((Matrix.fromRows A (D.map ι)).map ψ).mulVec := by
    have he : (Matrix.fromRows A (D.map ι)).map ψ = Matrix.fromRows (A.map ψ) D := by
      funext i j
      cases i <;> simp [Matrix.map_apply, Matrix.fromRows, hι]
    rw [he]
    exact haug
  have haugF := matrix_injective_of_specialization ι ψ hι φ hφ
    (Matrix.fromRows A (D.map ι)) haugR
  let V := LinearMap.ker (Matrix.toLin' (A.map φ))
  let g : V →ₗ[F] (Fin k → F) :=
    (Matrix.toLin' ((D.map ι).map φ)).comp V.subtype
  have hg : Function.Injective g := by
    intro v w h
    apply Subtype.ext
    apply haugF
    funext i
    cases i with
    | inl i =>
        change (A.map φ *ᵥ v.val) i = (A.map φ *ᵥ w.val) i
        rw [show A.map φ *ᵥ v.val = 0 from v.property,
          show A.map φ *ᵥ w.val = 0 from w.property]
    | inr i => exact congrFun h i
  have hd := LinearMap.finrank_le_finrank_of_injective hg
  simpa only [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] using hd

theorem polynomial_kernel_finrank_le_of_specialization
    {R K F a b : Type*} [CommRing R] [Field K] [Field F]
    [Fintype a] [Fintype b] [DecidableEq a] [DecidableEq b]
    (ι : K →+* R) (ψ : R →+* K) (hι : ∀ c, ψ (ι c) = c)
    (φ : R →+* F) (hφ : Function.Injective φ) (A : Matrix a b R[X]) (d : ℕ)
    (hAψ : DegreeBound (A.map (Polynomial.mapRingHom ψ)) 1)
    (hAφ : DegreeBound (A.map (Polynomial.mapRingHom φ)) 1) :
    Module.finrank F (polynomialKernelAtDegree (A.map (Polynomial.mapRingHom φ)) d) ≤
      Module.finrank K (polynomialKernelAtDegree (A.map (Polynomial.mapRingHom ψ)) d) := by
  rw [← coefficient_kernel_finrank _ d hAφ, ← coefficient_kernel_finrank _ d hAψ,
    polynomialCoefficientMatrix_map, polynomialCoefficientMatrix_map]
  exact matrix_kernel_finrank_le_of_specialization ι ψ hι φ hφ
    (polynomialCoefficientMatrix A d)

variable {K n m : Type*} [Field K] [Fintype n] [Fintype m]
  [DecidableEq n] [DecidableEq m]

/-- Every affine witness gives an upper bound for the actual generic SL
Hilbert function, including witnesses with nonzero, nonminimal nullity. -/
theorem generic_slHilbert_le_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ) :
    slHilbert (genericAffineSquare K n m) (genericAffineRows K n m) d ≤
      slHilbert M P d := by
  let ψ := affinePairSpecialization M P
  let φ := algebraMap (MvPolynomial (MatrixParameters n m ⊕ MatrixParameters n m) K)
    (AffineCoefficientField K (MatrixParameters n m))
  let A := slEquationMatrix (universalAffineSquare K n m) (universalAffineRows K n m) i₀
  have he : A.map (Polynomial.mapRingHom ψ) = slEquationMatrix M P i₀ := by
    dsimp only [A, ψ]
    rw [slEquationMatrix_map, universalAffineSquare_pair_specialization M P hM,
      universalAffineRows_pair_specialization M P hP]
  have hg : A.map (Polynomial.mapRingHom φ) =
      slEquationMatrix (genericAffineSquare K n m) (genericAffineRows K n m) i₀ := by
    dsimp only [A, φ]
    rw [slEquationMatrix_map, universalAffineSquare_generic, universalAffineRows_generic]
  have hs := polynomial_kernel_finrank_le_of_specialization MvPolynomial.C ψ
    (fun c => affinePairSpecialization_C M P c) φ (IsFractionRing.injective _ _) A d
    (by
      rw [he]
      exact slEquationMatrix_degree M P i₀ hM hP)
    (by
      rw [hg]
      exact slEquationMatrix_degree _ _ i₀
        (genericAffineSquare_degree K n m) (genericAffineRows_degree K n m))
  rw [slHilbert_eq_matrix_kernel _ _ i₀ d, slHilbert_eq_matrix_kernel _ _ i₀ d]
  rw [he, hg] at hs
  exact hs

theorem generic_boundedSLKernel_finrank_le_witness
    (M : Matrix n n K[X]) (P : Matrix m n K[X])
    (hM : DegreeBound M 1) (hP : DegreeBound P 1) (i₀ : n) (d : ℕ) :
    Module.finrank (AffineCoefficientField K (MatrixParameters n m))
      (boundedSLKernel (genericAffineSquare K n m) (genericAffineRows K n m) d) ≤
      Module.finrank K (boundedSLKernel M P d) :=
  generic_slHilbert_le_witness M P hM hP i₀ d

end FD56
