/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row20 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 20) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (20:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 21) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (21:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 22) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (22:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 23) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (23:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 24) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (24:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 25) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (25:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 26) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (26:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 27) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (27:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 28) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (28:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 29) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (29:Fin 67)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentCriticalInverseRows balancedTwentyThreeTangentCriticalSelectedColumns

theorem balancedTwentyThreeTangentCritical_inverse_residue_rows_2 (i j : Fin 67)
    (hlo : 20 ≤ i.val) (hhi : i.val < 30) :
    natListDot (balancedTwentyThreeTangentCriticalInverseRows i) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row20 j
  · exact inverse_row21 j
  · exact inverse_row22 j
  · exact inverse_row23 j
  · exact inverse_row24 j
  · exact inverse_row25 j
  · exact inverse_row26 j
  · exact inverse_row27 j
  · exact inverse_row28 j
  · exact inverse_row29 j

end FD56
