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

private theorem inverse_row95 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 95) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (95:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row96 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 96) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (96:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row97 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 97) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (97:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_19 (i j : Fin 98)
    (hlo : 95 ≤ i.val) (hhi : i.val < 98) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row95 j
  · exact inverse_row96 j
  · exact inverse_row97 j

end FD56
