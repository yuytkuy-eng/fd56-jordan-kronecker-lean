/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row0 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 0) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (0:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 1) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (1:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 2) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (2:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 3) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (3:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 4) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (4:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 5) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (5:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 6) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (6:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 7) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (7:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 8) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (8:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 9) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (9:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalInverseRows sixOutputTenSeedCriticalSelectedColumns

theorem sixOutputTenSeedCritical_inverse_residue_rows_0 (i j : Fin 54)
    (hlo : 0 ≤ i.val) (hhi : i.val < 10) :
    natListDot (sixOutputTenSeedCriticalInverseRows i) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j

end FD56
