/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedPolynomialRows0
import FD56.Hilbert.SixOutputEightSeedPolynomialRows1
import FD56.Hilbert.SixOutputEightSeedPolynomialRows2

/-! Exact equality between the actual tangent and its integral coefficients. -/

noncomputable section
namespace FD56
open Polynomial
variable {R : Type*} [CommRing R]
attribute [local irreducible] sixOutputEightSeedComputedData sixOutputEightSeedPolynomialData

private theorem polynomial_data_correct (i j : Fin 15) :
    integerPolynomialTrim (sixOutputEightSeedComputedData i j)=
      integerPolynomialTrim (sixOutputEightSeedPolynomialData i j) := by
  by_cases h0 : i.val<5
  · exact sixOutputEightSeed_polynomial_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputEightSeed_polynomial_rows_1 i j (by omega) h1
  exact sixOutputEightSeed_polynomial_rows_2 i j (by omega) i.isLt

theorem sixOutputEightSeedWitness_entry (i j : Fin 15) :
    sixOutputEightSeedWitness (R:=R) i j=integerPolynomial (sixOutputEightSeedPolynomialData i j) := by
  rw [← sixOutputEightSeed_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
