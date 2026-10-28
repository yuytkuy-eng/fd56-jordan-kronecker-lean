/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLData

/-! One row of the exact polynomial left-inverse certificate. -/

namespace FD56
set_option Elab.async false
set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem tenFour_left_entry_0_0 :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) (0 : Fin 5))=
      integerPolynomialTrim (if (0 : Fin 5)=(0 : Fin 5) then [tenFourLeftScale] else []) := by decide

private theorem tenFour_left_entry_0_1 :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) (1 : Fin 5))=
      integerPolynomialTrim (if (0 : Fin 5)=(1 : Fin 5) then [tenFourLeftScale] else []) := by decide

private theorem tenFour_left_entry_0_2 :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) (2 : Fin 5))=
      integerPolynomialTrim (if (0 : Fin 5)=(2 : Fin 5) then [tenFourLeftScale] else []) := by decide

private theorem tenFour_left_entry_0_3 :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) (3 : Fin 5))=
      integerPolynomialTrim (if (0 : Fin 5)=(3 : Fin 5) then [tenFourLeftScale] else []) := by decide

private theorem tenFour_left_entry_0_4 :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) (4 : Fin 5))=
      integerPolynomialTrim (if (0 : Fin 5)=(4 : Fin 5) then [tenFourLeftScale] else []) := by decide

theorem tenFour_left_row_0 (j : Fin 5) :
    integerPolynomialTrim (integerPolynomialMatrixProduct tenFourLeftData tenFourZData (0 : Fin 5) j)=
      integerPolynomialTrim (if (0 : Fin 5)=j then [tenFourLeftScale] else []) := by
  fin_cases j
  · exact tenFour_left_entry_0_0
  · exact tenFour_left_entry_0_1
  · exact tenFour_left_entry_0_2
  · exact tenFour_left_entry_0_3
  · exact tenFour_left_entry_0_4

end FD56
