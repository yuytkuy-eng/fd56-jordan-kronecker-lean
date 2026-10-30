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

private theorem inverse_row70 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 70) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (70:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row71 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 71) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (71:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row72 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 72) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (72:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row73 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 73) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (73:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row74 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 74) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (74:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_14 (i j : Fin 80)
    (hlo : 70 ≤ i.val) (hhi : i.val < 75) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row70 j
  · exact inverse_row71 j
  · exact inverse_row72 j
  · exact inverse_row73 j
  · exact inverse_row74 j

end FD56
