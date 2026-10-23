/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.MiddleGL

/-! Split polynomial kernel bases remain bases after coefficient extension. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K L a b r : Type*} [Field K] [Field L]
  [Fintype a] [Fintype b] [Fintype r]
  [DecidableEq a] [DecidableEq b] [DecidableEq r]

theorem polynomial_kernel_basis_split (A : Matrix a b K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' A)))
    (R : Matrix b a K[X]) (hR : A * R = 1) :
    ∃ S : Matrix r b K[X],
      S * polynomialKernelBasisMatrix A B = 1 ∧
      polynomialKernelBasisMatrix A B * S + R * A = 1 := by
  let V := polynomialKernelBasisMatrix A B
  have hV : A * V = 0 := polynomialKernelBasisMatrix_mul A B
  have hY : A * (1 - R * A) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, ← Matrix.mul_assoc, hR, Matrix.one_mul, sub_self]
  obtain ⟨S, hS⟩ := matrix_factor_through_kernel_basis A B (1 - R * A) hY
  change 1 - R * A = V * S at hS
  have hSV : S * V = 1 := by
    apply matrix_left_mul_injective_of_mulVec V (polynomialKernelBasisMatrix_injective A B)
    change V * (S * V) = V * 1
    rw [← Matrix.mul_assoc, ← hS, Matrix.sub_mul, Matrix.one_mul,
      Matrix.mul_assoc, hV, Matrix.mul_zero, sub_zero, Matrix.mul_one]
  refine ⟨S, hSV, ?_⟩
  rw [← hS, sub_add_cancel]

def splitPolynomialKernelEquiv (A : Matrix a b K[X]) (V : Matrix b r K[X])
    (S : Matrix r b K[X]) (R : Matrix b a K[X])
    (hAV : A * V = 0) (hSV : S * V = 1) (hVR : V * S + R * A = 1) :
    (r → K[X]) ≃ₗ[K[X]] LinearMap.ker (Matrix.toLin' A) where
  toFun c := ⟨V *ᵥ c, by
    change A *ᵥ (V *ᵥ c) = 0
    rw [Matrix.mulVec_mulVec, hAV, Matrix.zero_mulVec]⟩
  invFun y := S *ᵥ y.val
  left_inv c := by
    change S *ᵥ (V *ᵥ c) = c
    rw [Matrix.mulVec_mulVec, hSV, Matrix.one_mulVec]
  right_inv y := by
    apply Subtype.ext
    have hy : A *ᵥ y.val = 0 := y.property
    have h := congrArg (fun Z : Matrix b b K[X] => Z *ᵥ y.val) hVR
    dsimp only at h
    simp only [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hy,
      Matrix.mulVec_zero, add_zero, Matrix.one_mulVec] at h
    exact h
  map_add' c d := by apply Subtype.ext; exact Matrix.mulVec_add _ _ _
  map_smul' c d := by apply Subtype.ext; exact Matrix.mulVec_smul _ _ _

def splitPolynomialKernelBasis (A : Matrix a b K[X]) (V : Matrix b r K[X])
    (S : Matrix r b K[X]) (R : Matrix b a K[X])
    (hAV : A * V = 0) (hSV : S * V = 1) (hVR : V * S + R * A = 1) :
    Basis r K[X] (LinearMap.ker (Matrix.toLin' A)) :=
  (Pi.basisFun K[X] r).map (splitPolynomialKernelEquiv A V S R hAV hSV hVR)

omit [DecidableEq a] in
theorem polynomialKernelBasisMatrix_split (A : Matrix a b K[X]) (V : Matrix b r K[X])
    (S : Matrix r b K[X]) (R : Matrix b a K[X])
    (hAV : A * V = 0) (hSV : S * V = 1) (hVR : V * S + R * A = 1) :
    polynomialKernelBasisMatrix A (splitPolynomialKernelBasis A V S R hAV hSV hVR) = V := by
  funext i j
  change (V *ᵥ Pi.basisFun K[X] r j) i = V i j
  simp [Pi.basisFun_apply, Matrix.mulVec_single]

theorem polynomial_kernel_basis_map (σ : K →+* L) (A : Matrix a b K[X])
    (B : Basis r K[X] (LinearMap.ker (Matrix.toLin' A)))
    (R : Matrix b a K[X]) (hR : A * R = 1) :
    ∃ B' : Basis r L[X] (LinearMap.ker (Matrix.toLin' (A.map (Polynomial.mapRingHom σ)))),
      polynomialKernelBasisMatrix _ B' =
        (polynomialKernelBasisMatrix A B).map (Polynomial.mapRingHom σ) := by
  obtain ⟨S, hSV, hVR⟩ := polynomial_kernel_basis_split A B R hR
  let V := polynomialKernelBasisMatrix A B
  let φ := Polynomial.mapRingHom σ
  have hAV' : A.map φ * V.map φ = 0 := by
    rw [← Matrix.map_mul, polynomialKernelBasisMatrix_mul, Matrix.map_zero]
    exact map_zero φ
  have hSV' : S.map φ * V.map φ = 1 := by
    rw [← Matrix.map_mul, hSV, Matrix.map_one] <;> simp
  have hVR' : V.map φ * S.map φ + R.map φ * A.map φ = 1 := by
    rw [← Matrix.map_mul, ← Matrix.map_mul, ← Matrix.map_add, hVR, Matrix.map_one] <;> simp
  exact ⟨splitPolynomialKernelBasis _ _ _ _ hAV' hSV' hVR',
    polynomialKernelBasisMatrix_split _ _ _ _ hAV' hSV' hVR'⟩

end FD56
