/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedPolynomialRows0
import FD56.Hilbert.SixOutputTenSeedPolynomialRows1
import FD56.Hilbert.SixOutputTenSeedPolynomialRows2

/-! Exact equality between the actual tangent and its integral coefficients. -/

noncomputable section
namespace FD56
open Polynomial
variable {R : Type*} [CommRing R]
attribute [local irreducible] sixOutputTenSeedComputedData sixOutputTenSeedPolynomialData

private theorem polynomial_data_correct (i j : Fin 15) :
    integerPolynomialTrim (sixOutputTenSeedComputedData i j)=
      integerPolynomialTrim (sixOutputTenSeedPolynomialData i j) := by
  by_cases h0 : i.val<5
  · exact sixOutputTenSeed_polynomial_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputTenSeed_polynomial_rows_1 i j (by omega) h1
  exact sixOutputTenSeed_polynomial_rows_2 i j (by omega) i.isLt

theorem sixOutputTenSeedWitness_entry (i j : Fin 15) :
    sixOutputTenSeedWitness (R:=R) i j=integerPolynomial (sixOutputTenSeedPolynomialData i j) := by
  rw [← sixOutputTenSeed_computed_polynomial]
  exact integerPolynomial_eq_of_trim_eq (polynomial_data_correct i j)

end FD56
