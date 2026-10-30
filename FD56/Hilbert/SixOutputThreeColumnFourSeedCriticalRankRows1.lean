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

private theorem inverse_row5 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 5) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (5:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 6) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (6:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 7) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (7:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 8) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (8:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 9) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (9:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_1 (i j : Fin 98)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j

end FD56
