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

private theorem inverse_row40 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 40) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (40:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 41) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (41:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 42) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (42:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 43) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (43:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 44) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (44:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 45) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (45:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 46) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (46:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 47) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (47:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 48) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (48:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 49) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (49:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalInverseRows balancedEighteenTangentCriticalSelectedColumns

theorem balancedEighteenTangentCritical_inverse_residue_rows_4 (i j : Fin 54)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    natListDot (balancedEighteenTangentCriticalInverseRows i) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row40 j
  · exact inverse_row41 j
  · exact inverse_row42 j
  · exact inverse_row43 j
  · exact inverse_row44 j
  · exact inverse_row45 j
  · exact inverse_row46 j
  · exact inverse_row47 j
  · exact inverse_row48 j
  · exact inverse_row49 j

end FD56
