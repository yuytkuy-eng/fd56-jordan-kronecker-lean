/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailPolynomialRows0
import FD56.Hilbert.SixOutputThreeColumnTailPolynomialRows1
import FD56.Hilbert.SixOutputThreeColumnTailPolynomialRows2
import FD56.Hilbert.SixOutputThreeColumnTailPolynomialRows3

/-! Exact equality between the actual tangent and its integral coefficients. -/

noncomputable section
namespace FD56
open Polynomial
variable {R : Type*} [CommRing R]
attribute [local irreducible] sixOutputThreeColumnTailComputedData sixOutputThreeColumnTailPolynomialData

private theorem polynomial_data_correct (i j : Fin 20) :
    integerPolynomialTrim (sixOutputThreeColumnTailComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnTailPolynomialData i j) := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnTail_polynomial_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnTail_polynomial_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnTail_polynomial_rows_2 i j (by omega) h2
  exact sixOutputThreeColumnTail_polynomial_rows_3 i j (by omega) i.isLt

theorem sixOutputThreeColumnTailWitness_entry (i j : Fin 20) :
    sixOutputThreeColumnTailWitness (R:=R) i j=integerPolynomial (sixOutputThreeColumnTailPolynomialData i j) := by
  rw [← sixOutputThreeColumnTail_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
