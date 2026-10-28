/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.TenFourSLData

/-! Closed integer identities for one column of the mixed SL kernel certificate. -/
namespace FD56
open Matrix Polynomial
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false

theorem tenFour_integer_column2 :
    integerPolynomialTrim ((List.ofFn (fun i : Fin 10 => tenFourXData (2 : Fin 5) i i)).foldr
      integerPolynomialAdd [])=[] ∧
    (∀ (a : Fin 4) (b : Fin 10),
      integerPolynomialTrim (integerPolynomialMatrixProduct tenFourPData (tenFourXData (2 : Fin 5)) a b)=[]) ∧
    (∀ (a b : Fin 10),
      integerPolynomialTrim (integerPolynomialMatrixProduct tenFourMData (tenFourXData (2 : Fin 5)) a b)=
        integerPolynomialTrim (integerPolynomialAdd
          (integerPolynomialMatrixProduct (tenFourXData (2 : Fin 5)) tenFourMData a b)
          (integerPolynomialAdd (integerPolynomialMatrixProduct (tenFourUData (2 : Fin 5)) tenFourPData a b)
            (if a=b then tenFourScalarData (2 : Fin 5) else [])))) := by
  refine ⟨?_,?_,?_⟩
  · decide
  · decide
  · decide

end FD56
