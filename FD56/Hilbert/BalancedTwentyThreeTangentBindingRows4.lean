/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row40 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 40 j%101=(balancedTwentyThreeTangentSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 41 j%101=(balancedTwentyThreeTangentSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 42 j%101=(balancedTwentyThreeTangentSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 43 j%101=(balancedTwentyThreeTangentSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 44 j%101=(balancedTwentyThreeTangentSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 45 j%101=(balancedTwentyThreeTangentSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 46 j%101=(balancedTwentyThreeTangentSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 47 j%101=(balancedTwentyThreeTangentSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 48 j%101=(balancedTwentyThreeTangentSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 49 j%101=(balancedTwentyThreeTangentSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentSelectedIntegerEntry balancedTwentyThreeTangentSelectedData

theorem balancedTwentyThreeTangent_selected_integer_rows_4 (i j : Fin 60)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    balancedTwentyThreeTangentSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row40 j
  · exact selected_row41 j
  · exact selected_row42 j
  · exact selected_row43 j
  · exact selected_row44 j
  · exact selected_row45 j
  · exact selected_row46 j
  · exact selected_row47 j
  · exact selected_row48 j
  · exact selected_row49 j

end FD56
