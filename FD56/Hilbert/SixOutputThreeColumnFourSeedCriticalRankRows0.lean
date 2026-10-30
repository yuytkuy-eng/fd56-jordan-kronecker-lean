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

private theorem inverse_row0 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 0) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (0:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 1) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (1:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 2) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (2:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 3) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (3:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 4) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (4:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_0 (i j : Fin 98)
    (hlo : 0 ≤ i.val) (hhi : i.val < 5) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j

end FD56
