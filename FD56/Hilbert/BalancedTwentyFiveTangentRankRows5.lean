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

private theorem inverse_row50 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 50) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (50:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 51) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (51:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 52) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (52:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 53) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (53:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 54) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (54:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row55 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 55) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (55:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 56) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (56:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 57) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (57:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 58) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (58:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 59) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (59:Fin 70)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentInverseRows balancedTwentyFiveTangentSelectedColumns

theorem balancedTwentyFiveTangent_inverse_residue_rows_5 (i j : Fin 70)
    (hlo : 50 ≤ i.val) (hhi : i.val < 60) :
    natListDot (balancedTwentyFiveTangentInverseRows i) (balancedTwentyFiveTangentSelectedColumns j)%101=
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
