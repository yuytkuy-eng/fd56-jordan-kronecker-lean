/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row60 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 60 j%101=(balancedTwentyOneTangentCriticalSelectedData 60 j : ℤ) := by decide +kernel

private theorem selected_row61 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 61 j%101=(balancedTwentyOneTangentCriticalSelectedData 61 j : ℤ) := by decide +kernel

private theorem selected_row62 : ∀ j : Fin 63,
    balancedTwentyOneTangentCriticalSelectedIntegerEntry 62 j%101=(balancedTwentyOneTangentCriticalSelectedData 62 j : ℤ) := by decide +kernel

theorem balancedTwentyOneTangentCritical_selected_integer_rows_3 (i j : Fin 63)
    (hlo : 60 ≤ i.val) (hhi : i.val < 63) :
    balancedTwentyOneTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyOneTangentCriticalSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row60 j
  · exact selected_row61 j
  · exact selected_row62 j

end FD56
