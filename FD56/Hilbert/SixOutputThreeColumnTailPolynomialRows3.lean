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

private theorem polynomial_row15 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 15 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 15 j) := by decide +kernel

private theorem polynomial_row16 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 16 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 16 j) := by decide +kernel

private theorem polynomial_row17 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 17 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 17 j) := by decide +kernel

private theorem polynomial_row18 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 18 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 18 j) := by decide +kernel

private theorem polynomial_row19 : ∀ j : Fin 20,
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData 19 j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData 19 j) := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailComputedData sixOutputThreeColumnTailPolynomialData

theorem sixOutputThreeColumnTail_polynomial_rows_3 (i j : Fin 20)
    (hlo : 15 ≤ i.val) (hhi : i.val < 20) :
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData i j) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact polynomial_row15 j
  · exact polynomial_row16 j
  · exact polynomial_row17 j
  · exact polynomial_row18 j
  · exact polynomial_row19 j

end FD56
