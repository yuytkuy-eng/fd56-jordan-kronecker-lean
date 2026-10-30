/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row70 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 70) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (70:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row71 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 71) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (71:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row72 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 72) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (72:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row73 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 73) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (73:Fin 74)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalInverseRows balancedTwentyFiveTangentCriticalSelectedColumns

theorem balancedTwentyFiveTangentCritical_inverse_residue_rows_7 (i j : Fin 74)
    (hlo : 70 ≤ i.val) (hhi : i.val < 74) :
    natListDot (balancedTwentyFiveTangentCriticalInverseRows i) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row70 j
  · exact inverse_row71 j
  · exact inverse_row72 j
  · exact inverse_row73 j

end FD56
