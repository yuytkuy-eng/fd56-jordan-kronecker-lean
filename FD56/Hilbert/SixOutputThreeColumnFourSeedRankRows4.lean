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

private theorem inverse_row20 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 20) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (20:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 21) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (21:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 22) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (22:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 23) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (23:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 24) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (24:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_4 (i j : Fin 80)
    (hlo : 20 ≤ i.val) (hhi : i.val < 25) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row20 j
  · exact inverse_row21 j
  · exact inverse_row22 j
  · exact inverse_row23 j
  · exact inverse_row24 j

end FD56
