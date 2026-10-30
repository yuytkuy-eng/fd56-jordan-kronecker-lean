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

private theorem polynomial_row0 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 0 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 0 j) := by decide +kernel

private theorem polynomial_row1 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 1 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 1 j) := by decide +kernel

private theorem polynomial_row2 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 2 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 2 j) := by decide +kernel

private theorem polynomial_row3 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 3 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 3 j) := by decide +kernel

private theorem polynomial_row4 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 4 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 4 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedComputedData sixOutputThreeColumnFourSeedPolynomialData

theorem sixOutputThreeColumnFourSeed_polynomial_rows_0 (i j : Fin 20)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row0 j
  · exact polynomial_row1 j
  · exact polynomial_row2 j
  · exact polynomial_row3 j
  · exact polynomial_row4 j

end FD56
