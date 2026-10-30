/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedPolynomialBase

/-! Five exact rows of the integral polynomial coefficient binding. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem polynomial_row0 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 0 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 1 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 2 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 3 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 4 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 4 j) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedComputedData sixOutputTenSeedPolynomialData

theorem sixOutputTenSeed_polynomial_rows_0 (i j : Fin 15)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    integerPolynomialTrim (sixOutputTenSeedComputedData i j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

end FD56
