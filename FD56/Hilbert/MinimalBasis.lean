/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.ReducedBasis
import FD56.Hilbert.Basis

/-! Every polynomial matrix has a finite kernel basis whose leading columns
are independent. Its column degrees determine the entire kernel filtration. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]

theorem polynomial_kernel_has_minimal_basis (A : Matrix a b K[X]) :
    ∃ (r : ℕ) (B : Basis (Fin r) K[X] (LinearMap.ker (Matrix.toLin' A)))
      (e : Fin r → ℕ),
      (∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j) ∧
      Function.Injective (Matrix.mulVec
        (fun i j => (polynomialKernelBasisMatrix A B i j).coeff (e j))) ∧
      (∀ x : K, Function.Injective
        ((polynomialKernelBasisMatrix A B).map (Polynomial.evalRingHom x)).mulVec) ∧
      ∀ d : ℕ, Module.finrank K (polynomialKernelAtDegree A d) = ∑ j, (d + 1 - e j) := by
  obtain ⟨r, ⟨B₀⟩⟩ := polynomial_kernel_has_finite_basis A
  obtain ⟨B, hlead⟩ :=
    exists_reduced_polynomial_basis (LinearMap.ker (Matrix.toLin' A)) B₀
  let e : Fin r → ℕ := fun j => polynomialVectorDegree (B j).val
  have hdegree : ∀ i j, (polynomialKernelBasisMatrix A B i j).natDegree ≤ e j :=
    fun i j => polynomialVectorDegree_bound (B j).val i
  refine ⟨r, B, e, hdegree, hlead, ?_, ?_⟩
  · exact polynomialKernelBasisMatrix_pointwise_injective A B
  · intro d
    exact polynomial_kernel_basis_hilbert A B e d hdegree hlead

end FD56
