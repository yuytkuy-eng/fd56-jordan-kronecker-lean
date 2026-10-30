/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18Part0
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18Part1
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18Part2
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18Part3
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18Part4

/-! Five rows of the kernel-checked selected inverse. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 12000000

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

theorem sixOutputThreeColumnTail_inverse_residue_rows_18 (i j : Fin 120)
    (hlo : 90 ≤ i.val) (hhi : i.val < 95) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact sixOutputThreeColumnTail_inverse_numeric_row_90 j
  · exact sixOutputThreeColumnTail_inverse_numeric_row_91 j
  · exact sixOutputThreeColumnTail_inverse_numeric_row_92 j
  · exact sixOutputThreeColumnTail_inverse_numeric_row_93 j
  · exact sixOutputThreeColumnTail_inverse_numeric_row_94 j

end FD56
