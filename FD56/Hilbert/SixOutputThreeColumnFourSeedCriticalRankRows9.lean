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

private theorem inverse_row45 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 45) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (45:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 46) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (46:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 47) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (47:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 48) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (48:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 49) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (49:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_9 (i j : Fin 98)
    (hlo : 45 ≤ i.val) (hhi : i.val < 50) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row45 j
  · exact inverse_row46 j
  · exact inverse_row47 j
  · exact inverse_row48 j
  · exact inverse_row49 j

end FD56
