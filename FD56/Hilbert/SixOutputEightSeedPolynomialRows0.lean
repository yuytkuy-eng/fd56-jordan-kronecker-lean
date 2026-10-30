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

private theorem polynomial_row0 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 0 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 1 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 2 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 3 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀ j : Fin 15,
    integerPolynomialTrim (sixOutputEightSeedComputedData 4 j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData 4 j) := by decide +kernel

attribute [local irreducible] sixOutputEightSeedComputedData sixOutputEightSeedPolynomialData

theorem sixOutputEightSeed_polynomial_rows_0 (i j : Fin 15)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    integerPolynomialTrim (sixOutputEightSeedComputedData i j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

end FD56
