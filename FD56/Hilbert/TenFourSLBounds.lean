/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLLeftRow0
import FD56.Hilbert.TenFourSLLeftRow1
import FD56.Hilbert.TenFourSLLeftRow2
import FD56.Hilbert.TenFourSLLeftRow3
import FD56.Hilbert.TenFourSLLeftRow4

/-! Left-inverse and degree certificates for the ten-state SL witness. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000
variable {K : Type*} [Field K]

private theorem tenFour_left_certificate : ∀ i j : Fin 5,
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData i j)=
      integerPolynomialTrim (if i=j then [tenFourLeftScale] else []) := by
  intro i j
  fin_cases i
  · exact tenFour_left_row_0 j
  · exact tenFour_left_row_1 j
  · exact tenFour_left_row_2 j
  · exact tenFour_left_row_3 j
  · exact tenFour_left_row_4 j

theorem tenFour_left_scaled : (tenFourLeft (K:=K)*tenFourZ (K:=K) : Matrix (Fin 5) (Fin 5) K[X])=
    C (tenFourLeftScale : K) • (1 : Matrix (Fin 5) (Fin 5) K[X]) := by
  have h := integerPolynomialMatrix_mul_of_trim_eq (K:=K) tenFourLeftData tenFourZData
    (fun i j => if i=j then [tenFourLeftScale] else []) tenFour_left_certificate
  dsimp only [tenFourLeft,tenFourZ]
  rw [Matrix.submatrix_mul_equiv]
  change tenFourLeftRaw*tenFourZRaw=_
  rw [show tenFourLeftRaw (K:=K)*tenFourZRaw=
    integerPolynomialMatrix (fun i j : Fin 5 => if i=j then [tenFourLeftScale] else []) from h]
  funext i j
  by_cases hij : i=j <;>
    simp [integerPolynomialMatrix,hij,Matrix.smul_apply,Matrix.one_apply,C_eq_intCast]

theorem tenFour_column_degrees : ∀ i j, (tenFourZ (K:=K) i j).natDegree≤tenFourDegrees j := by
  have hlen : ∀ (i : Fin 140) (j : Fin 5), (tenFourZData i j).length≤tenFourDegrees j+1 := by decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (tenFourZData (tenFourInputEquiv i) j)).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hlen (tenFourInputEquiv i) j; omega)]
  simp

theorem tenFourM_degree : DegreeBound (tenFourM (K:=K)) 1 := by
  have hlen : ∀ i j, (tenFourMData i j).length≤2 := by decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (tenFourMData i j)).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hlen i j; omega)]
  simp

theorem tenFourP_degree : DegreeBound (tenFourP (K:=K)) 1 := by
  have hlen : ∀ i j, (tenFourPData i j).length≤2 := by decide
  intro i j
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  change (integerPolynomial (tenFourPData i j)).coeff k=0
  rw [integerPolynomial_coeff,List.getD_eq_default _ _ (by have := hlen i j; omega)]
  simp

end FD56
