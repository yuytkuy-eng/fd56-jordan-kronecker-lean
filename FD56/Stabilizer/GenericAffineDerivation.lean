/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Stabilizer.GenericPencil
import FD56.Stabilizer.GenericRows
import FD56.LinearAlgebra.FractionFieldDerivation
import FD56.LinearAlgebra.PolynomialCoefficientDerivation

/-! Every affine variation of the universal matrix pair is induced by a
derivation of its rational coefficient field. No characteristic restriction
or algebraic extension is needed. -/

noncomputable section
namespace FD56
open Matrix Polynomial

instance affineCoefficientBaseAlgebra (K σ : Type*) [Field K] :
    Algebra K (AffineCoefficientField K σ) :=
  inferInstanceAs (Algebra K (FractionRing (MvPolynomial (σ ⊕ σ) K)))

instance affineCoefficientBaseTower (K σ : Type*) [Field K] :
    IsScalarTower K (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ) :=
  inferInstanceAs (IsScalarTower K (MvPolynomial (σ ⊕ σ) K)
    (FractionRing (MvPolynomial (σ ⊕ σ) K)))

theorem generic_affine_parameter_derivation {K σ : Type*} [Field K]
    (v₀ v₁ : σ → AffineCoefficientField K σ) :
    ∃ D : Derivation K (AffineCoefficientField K σ) (AffineCoefficientField K σ),
      ∀ i, polynomialCoefficientDerivation D (affineParameterMap K σ (MvPolynomial.X i))=
        C (v₀ i)+X*C (v₁ i) := by
  obtain ⟨D,hD⟩ := rational_parameter_derivation_exists K (Sum.elim v₀ v₁)
  refine ⟨D,?_⟩
  intro i
  simp only [affineParameterMap,MvPolynomial.eval₂Hom_X',map_add,
    polynomialCoefficientDerivation_C,Derivation.leibniz,
    polynomialCoefficientDerivation_X,smul_eq_mul,mul_zero,add_zero,hD,
    Sum.elim_inl,Sum.elim_inr]
  have h₀ : D (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)
      (MvPolynomial.X (Sum.inl i)))=v₀ i := hD (Sum.inl i)
  have h₁ : D (algebraMap (MvPolynomial (σ ⊕ σ) K) (AffineCoefficientField K σ)
      (MvPolynomial.X (Sum.inr i)))=v₁ i := hD (Sum.inr i)
  exact congrArg₂ (fun a b : AffineCoefficientField K σ =>
    C a+(X : (AffineCoefficientField K σ)[X])*C b) h₀ h₁

theorem generic_affine_pair_derivation {K n m : Type*} [Field K]
    (A₀ A₁ : Matrix n n (AffineCoefficientField K (MatrixParameters n m)))
    (B₀ B₁ : Matrix m n (AffineCoefficientField K (MatrixParameters n m))) :
    ∃ D : Derivation K (AffineCoefficientField K (MatrixParameters n m))
        (AffineCoefficientField K (MatrixParameters n m)),
      (genericAffineSquare K n m).map (polynomialCoefficientDerivation D)=
        affineMatrixPencil A₀ A₁ ∧
      (genericAffineRows K n m).map (polynomialCoefficientDerivation D)=
        affineMatrixPencil B₀ B₁ := by
  obtain ⟨D,hD⟩ := generic_affine_parameter_derivation
    (Sum.elim (fun ij => A₀ ij.1 ij.2) (fun ij => B₀ ij.1 ij.2))
    (Sum.elim (fun ij => A₁ ij.1 ij.2) (fun ij => B₁ ij.1 ij.2))
  refine ⟨D,?_,?_⟩
  · funext i j
    exact hD (Sum.inl (i,j))
  · funext i j
    exact hD (Sum.inr (i,j))

end FD56
