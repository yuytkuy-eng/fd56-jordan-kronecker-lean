/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.LinearAlgebra.CoefficientMatrix

/-! Arbitrarily selected output coefficients detect bounded polynomial kernels. -/

noncomputable section
namespace FD56
open Matrix Polynomial
open scoped BigOperators
variable {K a b c : Type*} [Field K] [Fintype b]

def selectedPolynomialCoefficientMatrix (P : Matrix a b K[X]) (d : ℕ)
    (rows : c → a × ℕ) : Matrix c (b × Fin (d+1)) K :=
  fun i jl => (P (rows i).1 jl.1*X^jl.2.val).coeff (rows i).2

theorem selectedPolynomialCoefficientMatrix_mulVec [DecidableEq K]
    (P : Matrix a b K[X]) (d : ℕ) (rows : c → a × ℕ)
    (v : b × Fin (d+1) → K) (i : c) :
    (selectedPolynomialCoefficientMatrix P d rows *ᵥ v) i=
      ((P *ᵥ coefficientVectorPolynomial d v) (rows i).1).coeff (rows i).2 := by
  simp only [selectedPolynomialCoefficientMatrix,Matrix.mulVec,dotProduct,
    coefficientVectorPolynomial,Polynomial.ofFn_eq_sum_monomial,
    Finset.mul_sum,Polynomial.finset_sum_coeff,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  have hh : P (rows i).1 j*Polynomial.monomial l.val (v (j,l))=
      C (v (j,l))*(P (rows i).1 j*X^l.val) := by
    rw [← Polynomial.C_mul_X_pow_eq_monomial]
    ring
  rw [hh,Polynomial.coeff_C_mul]
  exact mul_comm _ _

theorem bounded_kernel_zero_of_selected_coefficient_injective
    (P : Matrix a b K[X]) (d : ℕ) (rows : c → a × ℕ)
    (hi : Function.Injective (selectedPolynomialCoefficientMatrix P d rows).mulVec)
    (v : b → K[X]) (hv : P *ᵥ v=0) (hdeg : ∀ j,(v j).natDegree≤d) : v=0 := by
  classical
  let z : b × Fin (d+1) → K := fun jl => (v jl.1).coeff jl.2.val
  have he : coefficientVectorPolynomial d z=v := by
    funext j
    exact Polynomial.ofFn_comp_toFn_eq_id_of_natDegree_lt
      (p := v j) (n := d+1) (by have := hdeg j; omega)
  have hz : selectedPolynomialCoefficientMatrix P d rows *ᵥ z=0 := by
    funext i
    rw [selectedPolynomialCoefficientMatrix_mulVec,he,hv]
    rfl
  have hzero : z=0 := hi (hz.trans (Matrix.mulVec_zero _).symm)
  rw [← he,hzero]
  funext j
  exact map_zero (Polynomial.ofFn (d+1))

end FD56
