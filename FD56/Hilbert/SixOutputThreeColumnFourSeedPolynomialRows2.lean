/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomialBase

/-! Five exact rows of the actual polynomial tangent binding. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

private theorem polynomial_row10 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 10 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 11 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 12 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 13 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 14 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 14 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedComputedData sixOutputThreeColumnFourSeedPolynomialData

theorem sixOutputThreeColumnFourSeed_polynomial_rows_2 (i j : Fin 20)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row10 j
  · exact polynomial_row11 j
  · exact polynomial_row12 j
  · exact polynomial_row13 j
  · exact polynomial_row14 j

end FD56
