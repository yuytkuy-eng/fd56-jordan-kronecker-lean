/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.PermutedSixOutputThreeTailData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 30,
    (permutedSixOutputThreeTailInverseRows i).length=30 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 30,
    (permutedSixOutputThreeTailSelectedColumns j).length=30 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 0) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (0:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 1) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (1:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 2) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (2:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 3) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (3:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 4) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (4:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 5) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (5:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 6) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (6:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 7) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (7:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 8) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (8:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 9) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (9:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 10) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (10:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 11) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (11:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 12) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (12:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 13) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (13:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 14) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (14:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 15) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (15:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 16) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (16:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 17) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (17:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 18) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (18:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 19) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (19:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 20) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (20:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 21) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (21:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 22) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (22:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 23) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (23:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 24) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (24:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 25) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (25:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 26) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (26:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 27) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (27:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 28) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (28:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 30,
    natListDot (permutedSixOutputThreeTailInverseRows 29) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if (29:Fin 30)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] permutedSixOutputThreeTailInverseRows permutedSixOutputThreeTailSelectedColumns

private theorem inverse_residues (i j : Fin 30) :
    natListDot (permutedSixOutputThreeTailInverseRows i) (permutedSixOutputThreeTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  fin_cases i
  · exact inverse_row0 j
  · exact inverse_row1 j
  · exact inverse_row2 j
  · exact inverse_row3 j
  · exact inverse_row4 j
  · exact inverse_row5 j
  · exact inverse_row6 j
  · exact inverse_row7 j
  · exact inverse_row8 j
  · exact inverse_row9 j
  · exact inverse_row10 j
  · exact inverse_row11 j
  · exact inverse_row12 j
  · exact inverse_row13 j
  · exact inverse_row14 j
  · exact inverse_row15 j
  · exact inverse_row16 j
  · exact inverse_row17 j
  · exact inverse_row18 j
  · exact inverse_row19 j
  · exact inverse_row20 j
  · exact inverse_row21 j
  · exact inverse_row22 j
  · exact inverse_row23 j
  · exact inverse_row24 j
  · exact inverse_row25 j
  · exact inverse_row26 j
  · exact inverse_row27 j
  · exact inverse_row28 j
  · exact inverse_row29 j

theorem permutedSixOutputThreeTailSelected_left_inverse :
    (show Matrix (Fin 30) (Fin 30) (ZMod 101) from
      fun i j => (permutedSixOutputThreeTailInverseRows i).getD j.val 0)*
      permutedSixOutputThreeTailSelected=1 := by
  exact matrix_inverse_of_natListDot 101 30 permutedSixOutputThreeTailInverseRows
    permutedSixOutputThreeTailSelectedColumns inverse_lengths column_lengths inverse_residues

theorem permutedSixOutputThreeTailSelected_injective :
    Function.Injective permutedSixOutputThreeTailSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse permutedSixOutputThreeTailSelected id
    _ permutedSixOutputThreeTailSelected_left_inverse

end FD56
