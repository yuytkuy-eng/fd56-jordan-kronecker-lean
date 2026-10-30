/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row0 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 0) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (0:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 1) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (1:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 2) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (2:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 3) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (3:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 4) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (4:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 5) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (5:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 6) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (6:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 7) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (7:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 8) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (8:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 9) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (9:Fin 69)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalInverseRows balancedTwentyFourTangentCriticalSelectedColumns

theorem balancedTwentyFourTangentCritical_inverse_residue_rows_0 (i j : Fin 69)
    (hlo : 0 ≤ i.val) (hhi : i.val < 10) :
    natListDot (balancedTwentyFourTangentCriticalInverseRows i) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j

end FD56
