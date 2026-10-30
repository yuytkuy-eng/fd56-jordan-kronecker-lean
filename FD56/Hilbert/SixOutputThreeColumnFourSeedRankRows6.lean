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

private theorem inverse_row30 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 30) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (30:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 31) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (31:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 32) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (32:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 33) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (33:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 34) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (34:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_6 (i j : Fin 80)
    (hlo : 30 ≤ i.val) (hhi : i.val < 35) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row30 j
  · exact inverse_row31 j
  · exact inverse_row32 j
  · exact inverse_row33 j
  · exact inverse_row34 j

end FD56
