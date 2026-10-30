/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.AllPolynomialCoefficients
import FD56.LinearAlgebra.SelectedPolynomialCoefficients

/-! A finite coefficient window computes the entire bounded kernel whenever
it contains the coefficients allowed by the matrix degree. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators

theorem full_selected_coefficient_kernel_finrank
    {K a b : Type*} [Field K] [Fintype b] [DecidableEq b]
    (P : Matrix a b K[X]) (D d : ℕ) (hP : DegreeBound P D) :
    Module.finrank K (LinearMap.ker (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix P d
        (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val))))) =
      Module.finrank K (polynomialKernelAtDegree P d) := by
  classical
  have he : LinearMap.ker (Matrix.toLin'
      (selectedPolynomialCoefficientMatrix P d
        (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val)))) =
      LinearMap.ker (Matrix.toLin' (allPolynomialCoefficientMatrix P d)) := by
    ext v
    change selectedPolynomialCoefficientMatrix P d
      (fun ik : a × Fin (D+d+1) => (ik.1,ik.2.val)) *ᵥ v=0 ↔
        allPolynomialCoefficientMatrix P d *ᵥ v=0
    constructor
    · intro hv
      apply (allPolynomialCoefficientMatrix_kernel_iff P d v).mpr
      funext i
      apply Polynomial.ext
      intro k
      by_cases hk : k<D+d+1
      · have h := congrFun hv (i,⟨k,hk⟩)
        rw [selectedPolynomialCoefficientMatrix_mulVec] at h
        exact h
      · have hdegree : ((P *ᵥ coefficientVectorPolynomial d v) i).natDegree≤D+d := by
          apply Polynomial.natDegree_sum_le_of_forall_le
          intro j _
          exact (Polynomial.natDegree_mul_le (p:=P i j)
            (q:=coefficientVectorPolynomial d v j)).trans
              (Nat.add_le_add (hP i j) (coefficientVectorPolynomial_degree d v j))
        exact Polynomial.coeff_eq_zero_of_natDegree_lt
          (lt_of_le_of_lt hdegree (by omega))
    · intro hv
      funext ik
      rw [selectedPolynomialCoefficientMatrix_mulVec]
      rw [(allPolynomialCoefficientMatrix_kernel_iff P d v).mp hv]
      rfl
  rw [he,all_coefficient_kernel_finrank]

end FD56
