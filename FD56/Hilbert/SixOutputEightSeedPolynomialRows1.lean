/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedPolynomialBase

/-! Five exact rows of the integral polynomial coefficient binding. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem polynomial_row5 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 5 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 5 j) := by decide +kernel

private theorem polynomial_row6 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 6 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 6 j) := by decide +kernel

private theorem polynomial_row7 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 7 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 7 j) := by decide +kernel

private theorem polynomial_row8 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 8 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 8 j) := by decide +kernel

private theorem polynomial_row9 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 9 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 9 j) := by decide +kernel

attribute [local irreducible] sixOutputEightSeedComputedData sixOutputEightSeedPolynomialData

theorem sixOutputEightSeed_polynomial_rows_1 (i j : Fin 15)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    integerPolynomialTrim (sixOutputEightSeedComputedData i j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row5 j
  · exact polynomial_row6 j
  · exact polynomial_row7 j
  · exact polynomial_row8 j
  · exact polynomial_row9 j

end FD56
