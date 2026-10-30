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

private theorem inverse_row80 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 80) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (80:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row81 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 81) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (81:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row82 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 82) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (82:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row83 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 83) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (83:Fin 98)=j then 1 else 0 := by decide +kernel

private theorem inverse_row84 : ∀ j : Fin 98,
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows 84) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if (84:Fin 98)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

theorem sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_16 (i j : Fin 98)
    (hlo : 80 ≤ i.val) (hhi : i.val < 85) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row80 j
  · exact inverse_row81 j
  · exact inverse_row82 j
  · exact inverse_row83 j
  · exact inverse_row84 j

end FD56
