/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row10 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 10) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (10:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 11) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (11:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 12) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (12:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 13) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (13:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 14) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (14:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 15) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (15:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 16) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (16:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 17) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (17:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 18) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (18:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 19) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (19:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalInverseRows balancedEighteenTangentCriticalSelectedColumns

theorem balancedEighteenTangentCritical_inverse_residue_rows_1 (i j : Fin 54)
    (hlo : 10 ≤ i.val) (hhi : i.val < 20) :
    natListDot (balancedEighteenTangentCriticalInverseRows i) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
  · exact inverse_row13 j
  · exact inverse_row14 j
  · exact inverse_row15 j
  · exact inverse_row16 j
  · exact inverse_row17 j
  · exact inverse_row18 j
  · exact inverse_row19 j

end FD56
