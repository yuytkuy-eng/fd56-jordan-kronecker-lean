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

private theorem inverse_row60 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 60) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (60:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 61) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (61:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 62) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (62:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row63 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 63) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (63:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row64 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 64) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (64:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row65 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 65) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (65:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row66 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 66) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (66:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row67 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 67) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (67:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row68 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 68) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (68:Fin 69)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalInverseRows balancedTwentyFourTangentCriticalSelectedColumns

theorem balancedTwentyFourTangentCritical_inverse_residue_rows_6 (i j : Fin 69)
    (hlo : 60 ≤ i.val) (hhi : i.val < 69) :
    natListDot (balancedTwentyFourTangentCriticalInverseRows i) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row60 j
  · exact inverse_row61 j
  · exact inverse_row62 j
  · exact inverse_row63 j
  · exact inverse_row64 j
  · exact inverse_row65 j
  · exact inverse_row66 j
  · exact inverse_row67 j
  · exact inverse_row68 j

end FD56
