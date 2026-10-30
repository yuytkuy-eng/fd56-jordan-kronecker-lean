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

private theorem inverse_row40 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 40) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (40:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 41) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (41:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 42) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (42:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 43) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (43:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 44) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (44:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 45) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (45:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 46) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (46:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 47) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (47:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 48) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (48:Fin 54)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 54,
    natListDot (sixOutputTenSeedCriticalInverseRows 49) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if (49:Fin 54)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputTenSeedCriticalInverseRows sixOutputTenSeedCriticalSelectedColumns

theorem sixOutputTenSeedCritical_inverse_residue_rows_4 (i j : Fin 54)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    natListDot (sixOutputTenSeedCriticalInverseRows i) (sixOutputTenSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row40 j
  · exact inverse_row41 j
  · exact inverse_row42 j
  · exact inverse_row43 j
  · exact inverse_row44 j
  · exact inverse_row45 j
  · exact inverse_row46 j
  · exact inverse_row47 j
  · exact inverse_row48 j
  · exact inverse_row49 j

end FD56
