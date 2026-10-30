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

private theorem inverse_row60 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 60) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (60:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 61) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (61:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 62) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (62:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 63) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (63:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 64) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (64:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row65 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 65) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (65:Fin 67)=j then 1 else 0 := by decide +kernel

private theorem inverse_row66 : ∀ j : Fin 67,
    natListDot (balancedTwentyThreeTangentCriticalInverseRows 66) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if (66:Fin 67)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentCriticalInverseRows balancedTwentyThreeTangentCriticalSelectedColumns

theorem balancedTwentyThreeTangentCritical_inverse_residue_rows_6 (i j : Fin 67)
    (hlo : 60 ≤ i.val) (hhi : i.val < 67) :
    natListDot (balancedTwentyThreeTangentCriticalInverseRows i) (balancedTwentyThreeTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j
  · exact inverse_row65 j
  · exact inverse_row66 j

end FD56
