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

private theorem inverse_row60 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 60) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (60:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 61) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (61:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 62) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (62:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 63) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (63:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 64) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (64:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_12 (i j : Fin 98)
    (hlo : 60 ≤ i.val) (hhi : i.val < 65) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j

end FD56
