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

private theorem inverse_row80 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 80) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (80:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row81 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 81) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (81:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row82 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 82) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (82:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row83 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 83) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (83:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row84 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 84) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (84:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_16 (i j : Fin 120)
    (hlo : 80 ≤ i.val) (hhi : i.val < 85) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row80 j
  · exact inverse_row81 j
  · exact inverse_row82 j
  · exact inverse_row83 j
  · exact inverse_row84 j

end FD56
