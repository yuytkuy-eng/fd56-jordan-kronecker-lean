/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.MixedKernelCoefficients
import FD56.LinearAlgebra.DualBasis

/-! Bounded functionals on a reduced kernel of an affine pencil lift to constant
or affine ambient vectors. This is a coefficient-level lifting statement. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a n j : Type*} [Field K] [Fintype n] [DecidableEq n] [Fintype j]

theorem polynomial_dual_constant_lift_of_coefficients
    (V : Matrix n j K[X]) (d : j → ℕ)
    (hdegree : ∀ i j, (V i j).natDegree ≤ d j)
    (hcoeff : Function.Injective (Matrix.mulVec
      (fun i (jk : Σ j, Fin (d j+1)) => (V i jk.1).coeff jk.2.val)))
    (p : j → K[X]) (hp : ∀ j, (p j).natDegree ≤ d j) :
    ∃ u : n → K, V.transpose *ᵥ (fun i => C (u i)) = p := by
  classical
  let E : Matrix n (Σ j, Fin (d j+1)) K :=
    fun i jk => (V i jk.1).coeff jk.2.val
  have hsurj : Function.Surjective E.transpose.mulVec :=
    matrix_surjective_of_transpose_injective E.transpose hcoeff
  obtain ⟨u,hu⟩ := hsurj (fun jk => (p jk.1).coeff jk.2.val)
  refine ⟨u, ?_⟩
  funext j
  apply Polynomial.ext
  intro k
  simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply,
    Polynomial.finset_sum_coeff, Polynomial.coeff_mul_C]
  by_cases hk : k < d j+1
  · exact congrFun hu ⟨j,⟨k,hk⟩⟩
  · have hVk (i : n) : (V i j).coeff k=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdegree i j) (by omega))
    have hpk : (p j).coeff k=0 :=
      Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hp j) (by omega))
    simp [hVk,hpk]

theorem affine_kernel_dual_constant_lift (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j))))
    (p : j → K[X]) (hp : ∀ j, (p j).natDegree ≤ d j) :
    ∃ u : n → K,
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis).transpose *ᵥ
        (fun i => C (u i)) = p :=
  polynomial_dual_constant_lift_of_coefficients _ d hdegree
    (mixed_kernel_basis_coefficients_injective A B basis d hdegree hlead) p hp

theorem affine_kernel_dual_affine_lift (A B : Matrix a n K)
    (basis : Basis j K[X] (LinearMap.ker (Matrix.toLin' (affineMatrixPencil A B))))
    (d : j → ℕ)
    (hdegree : ∀ i j, (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).natDegree ≤ d j)
    (hlead : Function.Injective (Matrix.mulVec
      (fun i j => (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis i j).coeff (d j))))
    (p : j → K[X]) (hp : ∀ j, (p j).natDegree ≤ d j+1) :
    ∃ u v : n → K,
      (polynomialKernelBasisMatrix (affineMatrixPencil A B) basis).transpose *ᵥ
        (fun i => C (u i) + X*C (v i)) = p := by
  classical
  let V := polynomialKernelBasisMatrix (affineMatrixPencil A B) basis
  let p₁ : j → K[X] := fun j => monomial (d j) ((p j).coeff (d j+1))
  let p₀ : j → K[X] := fun j => p j-X*p₁ j
  have hp₁ (j : j) : (p₁ j).natDegree ≤ d j := natDegree_monomial_le _
  have hp₀ (j : j) : (p₀ j).natDegree ≤ d j := by
    apply natDegree_le_iff_coeff_eq_zero.mpr
    intro k hk
    have hkpos : 0<k := by omega
    simp only [p₀,coeff_sub]
    rw [show k=(k-1)+1 by omega,coeff_X_mul]
    rw [show k-1+1=k by omega]
    by_cases hke : k=d j+1
    · subst k
      simp [p₁]
    · have hpk : (p j).coeff k=0 := coeff_eq_zero_of_natDegree_lt
        (lt_of_le_of_lt (hp j) (by omega))
      simp [p₁,coeff_monomial,hpk,show d j≠k-1 by omega]
  obtain ⟨u,hu⟩ := affine_kernel_dual_constant_lift A B basis d hdegree hlead p₀ hp₀
  obtain ⟨v,hv⟩ := affine_kernel_dual_constant_lift A B basis d hdegree hlead p₁ hp₁
  refine ⟨u,v,?_⟩
  change V.transpose *ᵥ ((fun i => C (u i)) + (X : K[X]) • (fun i => C (v i)))=p
  rw [Matrix.mulVec_add,Matrix.mulVec_smul,hu,hv]
  funext j
  simp [p₀,smul_eq_mul]

end FD56
