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

private theorem inverse_row20 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 20) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (20:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 21) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (21:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 22) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (22:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 23) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (23:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 24) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (24:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 25) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (25:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 26) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (26:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 27) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (27:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 28) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (28:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 29) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (29:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalInverseRows balancedEighteenTangentCriticalSelectedColumns

theorem balancedEighteenTangentCritical_inverse_residue_rows_2 (i j : Fin 54)
    (hlo : 20 ≤ i.val) (hhi : i.val < 30) :
    natListDot (balancedEighteenTangentCriticalInverseRows i) (balancedEighteenTangentCriticalSelectedColumns j)%101=
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
