/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.ObservabilityDeterminantDerivation
import FD56.Stabilizer.GenericAffineDerivation
import FD56.Hilbert.ObservabilityScalarFunctional

/-! The selected observability determinants have explicit SL kernel gradients.
Every affine variation of the generic pair acts through these same gradients. -/

noncomputable section
namespace FD56
open Matrix Polynomial
variable {B R K n m : Type*} [CommRing B] [CommRing R] [Algebra B R] [Field K]
  [Fintype n] [Fintype m] [DecidableEq n] [DecidableEq m]

theorem observabilityScalarLift_derivation_functional (D : Derivation B R R)
    (M : Matrix n n R) (P : Matrix m n R) (level : n → ℕ) (row : n → m) :
    matrixPairTraceFunctional (M.map D) (P.map D)
      (observabilityScalarLift M P level row)=
        D (observabilitySelectedMatrix M P level row).det := by
  simpa only [matrixPairTraceFunctional,observabilityScalarLift,LinearMap.coe_mk,
    AddHom.coe_mk,LinearEquiv.apply_symm_apply] using
      (observabilitySelectedMatrix_det_derivation D M P level row).symm

theorem observabilityScalarLift_sl_kernel
    (M : Matrix n n K[X]) (P : Matrix m n K[X]) (level : n → ℕ) (row : n → m)
    (hLower : ∀ k s, s<level k → ∀ a, ∃ l, level l=s ∧ row l=a) (i₀ : n) :
    slEquationMatrix M P i₀ *ᵥ observabilityScalarLift M P level row=0 := by
  letI : Nonempty n := ⟨i₀⟩
  apply (slEquationMatrix_kernel_iff _ _ _ _).mpr
  apply (slRadical_iff_equations _ _ _ _).mpr
  obtain ⟨hP,htrace,hcomm⟩ := observability_adjugate_scalar_equations M P level row hLower
  simp only [observabilityScalarLift,LinearEquiv.apply_symm_apply]
  exact ⟨htrace,hP,_,hcomm⟩

theorem generic_observability_minor_affine_variation
    (A₀ A₁ : Matrix n n (AffineCoefficientField K (MatrixParameters n m)))
    (B₀ B₁ : Matrix m n (AffineCoefficientField K (MatrixParameters n m))) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters n m))
        (AffineCoefficientField K (MatrixParameters n m)),
      ∀ (level : n → ℕ) (row : n → m),
        polynomialCoefficientDerivation D
          (observabilitySelectedMatrix (genericAffineSquare K n m)
            (genericAffineRows K n m) level row).det=
          matrixPairTraceFunctional (affineMatrixPencil A₀ A₁) (affineMatrixPencil B₀ B₁)
            (observabilityScalarLift (genericAffineSquare K n m)
              (genericAffineRows K n m) level row) := by
  obtain ⟨D,hM,hP⟩ := generic_affine_pair_derivation A₀ A₁ B₀ B₁
  refine ⟨D,?_⟩
  intro level row
  have h := observabilityScalarLift_derivation_functional (polynomialCoefficientDerivation D)
    (genericAffineSquare K n m) (genericAffineRows K n m) level row
  rw [hM,hP] at h
  exact h.symm

end FD56
