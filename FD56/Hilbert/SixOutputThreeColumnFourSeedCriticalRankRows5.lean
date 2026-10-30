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

private theorem inverse_row25 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 25) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (25:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 26) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (26:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 27) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (27:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 28) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (28:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 29) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (29:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_5 (i j : Fin 98)
    (hlo : 25 ≤ i.val) (hhi : i.val < 30) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row25 j
  · exact inverse_row26 j
  · exact inverse_row27 j
  · exact inverse_row28 j
  · exact inverse_row29 j

end FD56
