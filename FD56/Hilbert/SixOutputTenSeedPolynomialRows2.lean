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

private theorem polynomial_row10 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 10 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 11 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 12 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 13 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputTenSeedComputedData 14 j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData 14 j) := by decide +kernel

attribute [local irreducible] sixOutputTenSeedComputedData sixOutputTenSeedPolynomialData

theorem sixOutputTenSeed_polynomial_rows_2 (i j : Fin 15)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    integerPolynomialTrim (sixOutputTenSeedComputedData i j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row10 j
  · exact polynomial_row11 j
  · exact polynomial_row12 j
  · exact polynomial_row13 j
  · exact polynomial_row14 j

end FD56
