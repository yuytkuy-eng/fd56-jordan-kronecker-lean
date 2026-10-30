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

private theorem inverse_row55 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 55) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (55:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 56) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (56:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 57) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (57:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 58) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (58:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 59) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (59:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_11 (i j : Fin 80)
    (hlo : 55 ≤ i.val) (hhi : i.val < 60) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row55 j
  · exact inverse_row56 j
  · exact inverse_row57 j
  · exact inverse_row58 j
  · exact inverse_row59 j

end FD56
