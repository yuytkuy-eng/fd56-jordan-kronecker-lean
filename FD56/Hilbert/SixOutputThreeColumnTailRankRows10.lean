/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailData

/-! Five rows of the kernel-checked selected inverse. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 12000000

private theorem inverse_row50 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 50) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (50:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 51) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (51:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 52) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (52:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 53) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (53:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 54) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (54:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_10 (i j : Fin 120)
    (hlo : 50 ≤ i.val) (hhi : i.val < 55) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row50 j
  · exact inverse_row51 j
  · exact inverse_row52 j
  · exact inverse_row53 j
  · exact inverse_row54 j

end FD56
