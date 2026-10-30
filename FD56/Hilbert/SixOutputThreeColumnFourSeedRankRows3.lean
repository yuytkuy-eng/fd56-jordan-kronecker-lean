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

private theorem inverse_row15 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 15) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (15:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 16) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (16:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 17) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (17:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 18) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (18:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 19) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (19:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_3 (i j : Fin 80)
    (hlo : 15 ≤ i.val) (hhi : i.val < 20) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row15 j
  · exact inverse_row16 j
  · exact inverse_row17 j
  · exact inverse_row18 j
  · exact inverse_row19 j

end FD56
