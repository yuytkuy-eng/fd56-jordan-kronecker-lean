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

theorem sixOutputThreeColumnTail_inverse_numeric_row_91 : ∀ j : Fin 120,
    natListDot (sixOutputThreeColumnTailInverseRows 91) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if (91:Fin 120)=j then 1 else 0 := by decide +kernel

end FD56
