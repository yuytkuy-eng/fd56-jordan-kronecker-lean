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

private theorem inverse_row50 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 50) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (50:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 51) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (51:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 52) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (52:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 54,
    natListDot (balancedEighteenTangentCriticalInverseRows 53) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if (53:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedEighteenTangentCriticalInverseRows balancedEighteenTangentCriticalSelectedColumns

theorem balancedEighteenTangentCritical_inverse_residue_rows_5 (i j : Fin 54)
    (hlo : 50 ≤ i.val) (hhi : i.val < 54) :
    natListDot (balancedEighteenTangentCriticalInverseRows i) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row50 j
  · exact inverse_row51 j
  · exact inverse_row52 j
  · exact inverse_row53 j

end FD56
