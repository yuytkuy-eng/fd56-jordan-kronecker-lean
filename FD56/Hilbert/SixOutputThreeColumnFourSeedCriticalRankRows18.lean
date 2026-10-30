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

private theorem inverse_row90 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 90) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (90:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row91 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 91) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (91:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row92 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 92) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (92:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row93 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 93) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (93:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row94 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 94) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (94:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_18 (i j : Fin 98)
    (hlo : 90 ≤ i.val) (hhi : i.val < 95) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row90 j
  · exact inverse_row91 j
  · exact inverse_row92 j
  · exact inverse_row93 j
  · exact inverse_row94 j

end FD56
