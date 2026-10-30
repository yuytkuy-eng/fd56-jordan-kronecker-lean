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

private theorem selected_row40 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 40 j%101=(balancedTwentyFourTangentSelectedData 40 j : ℤ) := by decide +kernel

private theorem selected_row41 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 41 j%101=(balancedTwentyFourTangentSelectedData 41 j : ℤ) := by decide +kernel

private theorem selected_row42 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 42 j%101=(balancedTwentyFourTangentSelectedData 42 j : ℤ) := by decide +kernel

private theorem selected_row43 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 43 j%101=(balancedTwentyFourTangentSelectedData 43 j : ℤ) := by decide +kernel

private theorem selected_row44 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 44 j%101=(balancedTwentyFourTangentSelectedData 44 j : ℤ) := by decide +kernel

private theorem selected_row45 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 45 j%101=(balancedTwentyFourTangentSelectedData 45 j : ℤ) := by decide +kernel

private theorem selected_row46 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 46 j%101=(balancedTwentyFourTangentSelectedData 46 j : ℤ) := by decide +kernel

private theorem selected_row47 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 47 j%101=(balancedTwentyFourTangentSelectedData 47 j : ℤ) := by decide +kernel

private theorem selected_row48 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 48 j%101=(balancedTwentyFourTangentSelectedData 48 j : ℤ) := by decide +kernel

private theorem selected_row49 : ∀ j : Fin 60,
    balancedTwentyFourTangentSelectedIntegerEntry 49 j%101=(balancedTwentyFourTangentSelectedData 49 j : ℤ) := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentSelectedIntegerEntry balancedTwentyFourTangentSelectedData

theorem balancedTwentyFourTangent_selected_integer_rows_4 (i j : Fin 60)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    balancedTwentyFourTangentSelectedIntegerEntry i j%101=(balancedTwentyFourTangentSelectedData i j : ℤ) := by
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
