/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedData

/-! Exact inverse rows for one selected coefficient minor. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 12000000

private theorem inverse_row85 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 85) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (85:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row86 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 86) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (86:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row87 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 87) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (87:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row88 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 88) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (88:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row89 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 89) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (89:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_17 (i j : Fin 98)
    (hlo : 85 ≤ i.val) (hhi : i.val < 90) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row85 j
  · exact inverse_row86 j
  · exact inverse_row87 j
  · exact inverse_row88 j
  · exact inverse_row89 j

end FD56
