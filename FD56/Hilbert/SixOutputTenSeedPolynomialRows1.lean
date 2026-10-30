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

private theorem polynomial_row5 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 5 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 5 j) := by decide +kernel

private theorem polynomial_row6 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 6 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 6 j) := by decide +kernel

private theorem polynomial_row7 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 7 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 7 j) := by decide +kernel

private theorem polynomial_row8 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 8 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 8 j) := by decide +kernel

private theorem polynomial_row9 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 9 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 9 j) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedComputedData sixOutputTenSeedPolynomialData

theorem sixOutputTenSeed_polynomial_rows_1 (i j : Fin 15)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    integerPolynomialTrim (sixOutputTenSeedComputedData i j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row5 j
  · exact polynomial_row6 j
  · exact polynomial_row7 j
  · exact polynomial_row8 j
  · exact polynomial_row9 j

end FD56
