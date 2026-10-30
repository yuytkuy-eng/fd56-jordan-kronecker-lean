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

private theorem inverse_row50 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 50) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (50:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 51) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (51:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 52) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (52:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 53) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (53:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 54) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (54:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row55 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 55) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (55:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 56) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (56:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 57) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (57:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 58) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (58:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 59) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (59:Fin 74)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalInverseRows balancedTwentyFiveTangentCriticalSelectedColumns

theorem balancedTwentyFiveTangentCritical_inverse_residue_rows_5 (i j : Fin 74)
    (hlo : 50 ≤ i.val) (hhi : i.val < 60) :
    natListDot (balancedTwentyFiveTangentCriticalInverseRows i) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row50 j
  · exact inverse_row51 j
  · exact inverse_row52 j
  · exact inverse_row53 j
  · exact inverse_row54 j
  · exact inverse_row55 j
  · exact inverse_row56 j
  · exact inverse_row57 j
  · exact inverse_row58 j
  · exact inverse_row59 j

end FD56
