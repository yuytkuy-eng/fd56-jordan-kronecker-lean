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

private theorem polynomial_row5 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 5 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 5 j) := by decide +kernel

private theorem polynomial_row6 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 6 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 6 j) := by decide +kernel

private theorem polynomial_row7 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 7 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 7 j) := by decide +kernel

private theorem polynomial_row8 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 8 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 8 j) := by decide +kernel

private theorem polynomial_row9 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 9 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 9 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailComputedData sixOutputThreeColumnTailPolynomialData

theorem sixOutputThreeColumnTail_polynomial_rows_1 (i j : Fin 20)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row5 j
  · exact polynomial_row6 j
  · exact polynomial_row7 j
  · exact polynomial_row8 j
  · exact polynomial_row9 j

end FD56
