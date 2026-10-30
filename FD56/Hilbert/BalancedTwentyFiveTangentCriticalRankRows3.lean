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

private theorem inverse_row30 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 30) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (30:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 31) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (31:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 32) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (32:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 33) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (33:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 34) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (34:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 35) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (35:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 36) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (36:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 37) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (37:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 38) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (38:Fin 74)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 74,
    natListDot (balancedTwentyFiveTangentCriticalInverseRows 39) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if (39:Fin 74)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentCriticalInverseRows balancedTwentyFiveTangentCriticalSelectedColumns

theorem balancedTwentyFiveTangentCritical_inverse_residue_rows_3 (i j : Fin 74)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    natListDot (balancedTwentyFiveTangentCriticalInverseRows i) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row30 j
  · exact inverse_row31 j
  · exact inverse_row32 j
  · exact inverse_row33 j
  · exact inverse_row34 j
  · exact inverse_row35 j
  · exact inverse_row36 j
  · exact inverse_row37 j
  · exact inverse_row38 j
  · exact inverse_row39 j

end FD56
