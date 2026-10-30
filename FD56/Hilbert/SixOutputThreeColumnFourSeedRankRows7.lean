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

private theorem inverse_row35 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 35) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (35:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 36) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (36:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 37) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (37:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 38) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (38:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 39) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (39:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_7 (i j : Fin 80)
    (hlo : 35 ≤ i.val) (hhi : i.val < 40) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row35 j
  · exact inverse_row36 j
  · exact inverse_row37 j
  · exact inverse_row38 j
  · exact inverse_row39 j

end FD56
