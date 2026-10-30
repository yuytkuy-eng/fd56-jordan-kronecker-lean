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

private theorem inverse_row5 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 5) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (5:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 6) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (6:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 7) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (7:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 8) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (8:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 9) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (9:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_1 (i j : Fin 80)
    (hlo : 5 ≤ i.val) (hhi : i.val < 10) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j

end FD56
