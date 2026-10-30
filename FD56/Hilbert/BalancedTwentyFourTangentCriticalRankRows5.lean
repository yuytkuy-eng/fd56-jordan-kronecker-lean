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

private theorem inverse_row50 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 50) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (50:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 51) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (51:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 52) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (52:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 53) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (53:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 54) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (54:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row55 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 55) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (55:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 56) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (56:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 57) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (57:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 58) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (58:Fin 69)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 69,
    natListDot (balancedTwentyFourTangentCriticalInverseRows 59) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if (59:Fin 69)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyFourTangentCriticalInverseRows balancedTwentyFourTangentCriticalSelectedColumns

theorem balancedTwentyFourTangentCritical_inverse_residue_rows_5 (i j : Fin 69)
    (hlo : 50 ≤ i.val) (hhi : i.val < 60) :
    natListDot (balancedTwentyFourTangentCriticalInverseRows i) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i <;> norm_num at hlo hhi
  · exact inverse_row50 j
  · exact inverse_row51 j
  · exact inverse_row52 j
  · exact inverse_row53 j
  · exact inverse_row54 j
  · exact inverse_row55 j
  · exact inverse_row56 j
  · exact inverse_row57 j
  · exact inverse_row58 j
  · exact inverse_row59 j

end FD56
