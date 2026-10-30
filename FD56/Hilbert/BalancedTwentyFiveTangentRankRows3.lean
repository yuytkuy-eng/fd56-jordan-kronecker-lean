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

private theorem inverse_row30 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 30) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (30:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 31) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (31:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 32) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (32:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 33) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (33:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 34) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (34:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 35) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (35:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 36) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (36:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 37) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (37:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 38) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (38:Fin 70)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 70,
    natListDot (balancedTwentyFiveTangentInverseRows 39) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if (39:Fin 70)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFiveTangentInverseRows balancedTwentyFiveTangentSelectedColumns

theorem balancedTwentyFiveTangent_inverse_residue_rows_3 (i j : Fin 70)
    (hlo : 30 ≤ i.val) (hhi : i.val < 40) :
    natListDot (balancedTwentyFiveTangentInverseRows i) (balancedTwentyFiveTangentSelectedColumns j)%101=
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
