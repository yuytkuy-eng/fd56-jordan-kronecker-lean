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

private theorem polynomial_row10 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 10 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 11 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 12 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 13 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 14 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 14 j) := by decide +kernel

attribute [local irreducible] sixOutputEightSeedComputedData sixOutputEightSeedPolynomialData

theorem sixOutputEightSeed_polynomial_rows_2 (i j : Fin 15)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    integerPolynomialTrim (sixOutputEightSeedComputedData i j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row10 j
  · exact polynomial_row11 j
  · exact polynomial_row12 j
  · exact polynomial_row13 j
  · exact polynomial_row14 j

end FD56
