/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomialRows0
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomialRows1
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomialRows2
import FD56.Hilbert.SixOutputThreeColumnFourSeedPolynomialRows3

/-! Exact equality between the actual tangent and its integral coefficients. -/

noncomputable section
namespace FD56
open Polynomial
variable {R : Type*} [CommRing R]
attribute [local irreducible] sixOutputThreeColumnFourSeedComputedData sixOutputThreeColumnFourSeedPolynomialData

private theorem polynomial_data_correct (i j : Fin 20) :
    integerPolynomialTrim (sixOutputThreeColumnFourSeedComputedData i j)=
      integerPolynomialTrim (sixOutputThreeColumnFourSeedPolynomialData i j) := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnFourSeed_polynomial_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnFourSeed_polynomial_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnFourSeed_polynomial_rows_2 i j (by omega) h2
  exact sixOutputThreeColumnFourSeed_polynomial_rows_3 i j (by omega) i.isLt

theorem sixOutputThreeColumnFourSeedWitness_entry (i j : Fin 20) :
    sixOutputThreeColumnFourSeedWitness (R:=R) i j=integerPolynomial (sixOutputThreeColumnFourSeedPolynomialData i j) := by
  rw [← sixOutputThreeColumnFourSeed_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
