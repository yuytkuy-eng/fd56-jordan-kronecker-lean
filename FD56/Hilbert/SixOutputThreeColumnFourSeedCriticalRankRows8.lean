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

private theorem inverse_row40 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 40) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (40:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 41) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (41:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 42) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (42:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 43) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (43:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 44) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (44:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_8 (i j : Fin 98)
    (hlo : 40 ≤ i.val) (hhi : i.val < 45) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row40 j
  · exact inverse_row41 j
  · exact inverse_row42 j
  · exact inverse_row43 j
  · exact inverse_row44 j

end FD56
