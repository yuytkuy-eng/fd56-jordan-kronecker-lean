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

private theorem inverse_row20 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 20) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (20:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 21) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (21:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 22) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (22:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 23) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (23:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 24) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (24:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_4 (i j : Fin 98)
    (hlo : 20 ≤ i.val) (hhi : i.val < 25) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row20 j
  · exact inverse_row21 j
  · exact inverse_row22 j
  · exact inverse_row23 j
  · exact inverse_row24 j

end FD56
