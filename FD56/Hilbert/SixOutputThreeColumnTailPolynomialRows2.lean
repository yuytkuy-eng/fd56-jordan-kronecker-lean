/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailPolynomialBase

/-! Five exact rows of the actual polynomial tangent binding. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 3000000

private theorem polynomial_row10 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 10 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 10 j) := by decide +kernel

private theorem polynomial_row11 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 11 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 11 j) := by decide +kernel

private theorem polynomial_row12 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 12 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 12 j) := by decide +kernel

private theorem polynomial_row13 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 13 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 13 j) := by decide +kernel

private theorem polynomial_row14 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 14 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 14 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailComputedData sixOutputThreeColumnTailPolynomialData

theorem sixOutputThreeColumnTail_polynomial_rows_2 (i j : Fin 20)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row10 j
  · exact polynomial_row11 j
  · exact polynomial_row12 j
  · exact polynomial_row13 j
  · exact polynomial_row14 j

end FD56
