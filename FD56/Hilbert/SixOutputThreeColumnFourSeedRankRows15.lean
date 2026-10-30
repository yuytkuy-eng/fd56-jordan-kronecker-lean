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

private theorem inverse_row75 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 75) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (75:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row76 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 76) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (76:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row77 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 77) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (77:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row78 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 78) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (78:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row79 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 79) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (79:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_15 (i j : Fin 80)
    (hlo : 75 ≤ i.val) (hhi : i.val < 80) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row75 j
  · exact inverse_row76 j
  · exact inverse_row77 j
  · exact inverse_row78 j
  · exact inverse_row79 j

end FD56
