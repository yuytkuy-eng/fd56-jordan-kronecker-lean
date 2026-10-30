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

private theorem inverse_row35 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 35) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (35:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 36) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (36:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 37) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (37:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 38) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (38:Fin 120)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 39) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (39:Fin 120)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_7 (i j : Fin 120)
    (hlo : 35 ≤ i.val) (hhi : i.val < 40) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row35 j
  · exact inverse_row36 j
  · exact inverse_row37 j
  · exact inverse_row38 j
  · exact inverse_row39 j

end FD56
