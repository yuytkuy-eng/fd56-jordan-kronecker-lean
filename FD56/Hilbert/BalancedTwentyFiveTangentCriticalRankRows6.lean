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

private theorem inverse_row60 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 60) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (60:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 61) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (61:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 62) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (62:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 63) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (63:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 64) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (64:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row65 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 65) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (65:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row66 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 66) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (66:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row67 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 67) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (67:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row68 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 68) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (68:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row69 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 69) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (69:Fin 74)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalInverseRows balancedTwentyFiveTangentCriticalSelectedColumns

theorem balancedTwentyFiveTangentCritical_inverse_residue_rows_6 (i j : Fin 74)
    (hlo : 60 ≤ i.val) (hhi : i.val < 70) :
    natListDot (balancedTwentyFiveTangentCriticalInverseRows i) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j
  · exact inverse_row65 j
  · exact inverse_row66 j
  · exact inverse_row67 j
  · exact inverse_row68 j
  · exact inverse_row69 j

end FD56
