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

private theorem inverse_row65 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 65) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (65:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row66 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 66) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (66:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row67 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 67) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (67:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row68 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 68) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (68:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row69 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 69) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (69:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_13 (i j : Fin 120)
    (hlo : 65 ≤ i.val) (hhi : i.val < 70) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row65 j
  · exact inverse_row66 j
  · exact inverse_row67 j
  · exact inverse_row68 j
  · exact inverse_row69 j

end FD56
