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

private theorem inverse_row60 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 60) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (60:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 61) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (61:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 62) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (62:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 63) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (63:Fin 80)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 80,
    natListDot (sixOutputThreeColumnFourSeedInverseRows 64) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if (64:Fin 80)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

theorem sixOutputThreeColumnFourSeed_inverse_residue_rows_12 (i j : Fin 80)
    (hlo : 60 ≤ i.val) (hhi : i.val < 65) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j

end FD56
