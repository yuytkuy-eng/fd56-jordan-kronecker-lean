/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentData

/-! A bounded block of kernel-checked selected inverse identities. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_row40 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 40) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (40:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 41) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (41:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 42) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (42:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 43) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (43:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 44) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (44:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 45) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (45:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 46) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (46:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 47) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (47:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 48) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (48:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 49) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (49:Fin 69)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalInverseRows balancedTwentyFourTangentCriticalSelectedColumns

theorem balancedTwentyFourTangentCritical_inverse_residue_rows_4 (i j : Fin 69)
    (hlo : 40 ≤ i.val) (hhi : i.val < 50) :
    natListDot (balancedTwentyFourTangentCriticalInverseRows i) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row40 j
  · exact inverse_row41 j
  · exact inverse_row42 j
  · exact inverse_row43 j
  · exact inverse_row44 j
  · exact inverse_row45 j
  · exact inverse_row46 j
  · exact inverse_row47 j
  · exact inverse_row48 j
  · exact inverse_row49 j

end FD56
