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

private theorem polynomial_row15 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 15 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 15 j) := by decide +kernel

private theorem polynomial_row16 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 16 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 16 j) := by decide +kernel

private theorem polynomial_row17 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 17 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 17 j) := by decide +kernel

private theorem polynomial_row18 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 18 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 18 j) := by decide +kernel

private theorem polynomial_row19 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData 19 j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData 19 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedComputedData sixOutputThreeColumnFourSeedPolynomialData

theorem sixOutputThreeColumnFourSeed_polynomial_rows_3 (i j : Fin 20)
    (hlo : 15 ≤ i.val) (hhi : i.val < 20) :
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row15 j
  · exact polynomial_row16 j
  · exact polynomial_row17 j
  · exact polynomial_row18 j
  · exact polynomial_row19 j

end FD56
