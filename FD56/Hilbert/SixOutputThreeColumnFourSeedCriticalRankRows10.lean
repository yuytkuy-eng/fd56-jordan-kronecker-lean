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

private theorem inverse_row50 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 50) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (50:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 51) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (51:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 52) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (52:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 53) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (53:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 54) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (54:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_10 (i j : Fin 98)
    (hlo : 50 ≤ i.val) (hhi : i.val < 55) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row50 j
  · exact inverse_row51 j
  · exact inverse_row52 j
  · exact inverse_row53 j
  · exact inverse_row54 j

end FD56
