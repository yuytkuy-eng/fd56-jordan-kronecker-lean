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

private theorem inverse_row10 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 10) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (10:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 11) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (11:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 12) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (12:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 13) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (13:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 14) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (14:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_2 (i j : Fin 98)
    (hlo : 10 ≤ i.val) (hhi : i.val < 15) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
  · exact inverse_row13 j
  · exact inverse_row14 j

end FD56
