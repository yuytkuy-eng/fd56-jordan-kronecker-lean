/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.SelectedPolynomialCoefficients

/-! All output coefficients detect bounded polynomial kernels for matrices
of arbitrary degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

variable {K a b : Type*} [Field K] [Fintype b]

private theorem full_coefficient_kernel_zero [DecidableEq K]
    (P : Matrix a b K[X]) (D d : ℕ) (hP : DegreeBound P D)
    (v : b × Fin (d+1) → K)
    (hv : selectedPolynomialCoefficientMatrix P d
      (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val)) *ᵥ v=0) :
    P *ᵥ coefficientVectorPolynomial d v=0 := by
  funext i
  apply Polynomial.ext
  intro k
  by_cases hk : k<D+d+1
  · have h := congrFun hv (i,⟨k,hk⟩)
    rw [selectedPolynomialCoefficientMatrix_mulVec] at h
    exact h
  · change ((P *ᵥ coefficientVectorPolynomial d v) i).coeff k=0
    have hdegree : ((P *ᵥ coefficientVectorPolynomial d v) i).natDegree≤D+d := by
      apply Polynomial.natDegree_sum_le_of_forall_le
      intro j _
      exact (Polynomial.natDegree_mul_le (p:=P i j)
        (q:=coefficientVectorPolynomial d v j)).trans
          (Nat.add_le_add (hP i j) (coefficientVectorPolynomial_degree d v j))
    exact Polynomial.coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt hdegree (by omega))

theorem full_selected_coefficient_injective_of_bounded_kernel_zero
    (P : Matrix a b K[X]) (D d : ℕ) (hP : DegreeBound P D)
    (hz : ∀ v : b → K[X], P *ᵥ v=0 → (∀ j, (v j).natDegree≤d) → v=0) :
    Function.Injective (selectedPolynomialCoefficientMatrix P d
      (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val))).mulVec := by
  classical
  change Function.Injective (Matrix.toLin' (selectedPolynomialCoefficientMatrix P d
    (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val))))
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro v hv
  have hh := hz (coefficientVectorPolynomial d v)
    (full_coefficient_kernel_zero P D d hP v hv) (coefficientVectorPolynomial_degree d v)
  funext jl
  have he := congrArg (fun p : K[X] => p.coeff jl.2.val) (congrFun hh jl.1)
  simpa [coefficientVectorPolynomial] using he

end FD56
