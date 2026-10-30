/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentBindingBase

/-! A bounded block of exact selected coefficient identities. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 2000000

private theorem selected_row30 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 30 j%101=(balancedTwentyFourTangentSelectedData 30 j : ℤ) := by decide +kernel

private theorem selected_row31 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 31 j%101=(balancedTwentyFourTangentSelectedData 31 j : ℤ) := by decide +kernel

private theorem selected_row32 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 32 j%101=(balancedTwentyFourTangentSelectedData 32 j : ℤ) := by decide +kernel

private theorem selected_row33 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 33 j%101=(balancedTwentyFourTangentSelectedData 33 j : ℤ) := by decide +kernel

private theorem selected_row34 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 34 j%101=(balancedTwentyFourTangentSelectedData 34 j : ℤ) := by decide +kernel

private theorem selected_row35 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 35 j%101=(balancedTwentyFourTangentSelectedData 35 j : ℤ) := by decide +kernel

private theorem selected_row36 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 36 j%101=(balancedTwentyFourTangentSelectedData 36 j : ℤ) := by decide +kernel

private theorem selected_row37 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 37 j%101=(balancedTwentyFourTangentSelectedData 37 j : ℤ) := by decide +kernel

private theorem selected_row38 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 38 j%101=(balancedTwentyFourTangentSelectedData 38 j : ℤ) := by decide +kernel

private theorem selected_row39 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 39 j%101=(balancedTwentyFourTangentSelectedData 39 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentSelectedIntegerEntry balancedTwentyFourTangentSelectedData

theorem balancedTwentyFourTangent_selected_integer_rows_3 (i j : Fin 60)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    balancedTwentyFourTangentSelectedIntegerEntry i j%101=(balancedTwentyFourTangentSelectedData i j : ℤ) := by
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
