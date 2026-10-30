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

private theorem selected_row30 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 30 j%101=(balancedTwentyThreeTangentSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 31 j%101=(balancedTwentyThreeTangentSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 32 j%101=(balancedTwentyThreeTangentSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 33 j%101=(balancedTwentyThreeTangentSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 34 j%101=(balancedTwentyThreeTangentSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 35 j%101=(balancedTwentyThreeTangentSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 36 j%101=(balancedTwentyThreeTangentSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 37 j%101=(balancedTwentyThreeTangentSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 38 j%101=(balancedTwentyThreeTangentSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 60,
    balancedTwentyThreeTangentSelectedIntegerEntry 39 j%101=(balancedTwentyThreeTangentSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentSelectedIntegerEntry balancedTwentyThreeTangentSelectedData

theorem balancedTwentyThreeTangent_selected_integer_rows_3 (i j : Fin 60)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    balancedTwentyThreeTangentSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentSelectedData i j : ℤ) := by
  fin_cases i <;> norm_num at hlo hhi
  · exact selected_row30 j
  · exact selected_row31 j
  · exact selected_row32 j
  · exact selected_row33 j
  · exact selected_row34 j
  · exact selected_row35 j
  · exact selected_row36 j
  · exact selected_row37 j
  · exact selected_row38 j
  · exact selected_row39 j

end FD56
