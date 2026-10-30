/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputEightSeedData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 30,
    (sixOutputEightSeedInverseRows i).length=30 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 30,
    (sixOutputEightSeedSelectedColumns j).length=30 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 0) (sixOutputEightSeedSelectedColumns j)%101=
      if (0:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 1) (sixOutputEightSeedSelectedColumns j)%101=
      if (1:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 2) (sixOutputEightSeedSelectedColumns j)%101=
      if (2:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 3) (sixOutputEightSeedSelectedColumns j)%101=
      if (3:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 4) (sixOutputEightSeedSelectedColumns j)%101=
      if (4:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 5) (sixOutputEightSeedSelectedColumns j)%101=
      if (5:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 6) (sixOutputEightSeedSelectedColumns j)%101=
      if (6:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 7) (sixOutputEightSeedSelectedColumns j)%101=
      if (7:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 8) (sixOutputEightSeedSelectedColumns j)%101=
      if (8:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 9) (sixOutputEightSeedSelectedColumns j)%101=
      if (9:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 10) (sixOutputEightSeedSelectedColumns j)%101=
      if (10:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 11) (sixOutputEightSeedSelectedColumns j)%101=
      if (11:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 12) (sixOutputEightSeedSelectedColumns j)%101=
      if (12:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 13) (sixOutputEightSeedSelectedColumns j)%101=
      if (13:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 14) (sixOutputEightSeedSelectedColumns j)%101=
      if (14:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 15) (sixOutputEightSeedSelectedColumns j)%101=
      if (15:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 16) (sixOutputEightSeedSelectedColumns j)%101=
      if (16:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 17) (sixOutputEightSeedSelectedColumns j)%101=
      if (17:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 18) (sixOutputEightSeedSelectedColumns j)%101=
      if (18:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 19) (sixOutputEightSeedSelectedColumns j)%101=
      if (19:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 20) (sixOutputEightSeedSelectedColumns j)%101=
      if (20:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 21) (sixOutputEightSeedSelectedColumns j)%101=
      if (21:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 22) (sixOutputEightSeedSelectedColumns j)%101=
      if (22:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 23) (sixOutputEightSeedSelectedColumns j)%101=
      if (23:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 24) (sixOutputEightSeedSelectedColumns j)%101=
      if (24:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 25) (sixOutputEightSeedSelectedColumns j)%101=
      if (25:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 26) (sixOutputEightSeedSelectedColumns j)%101=
      if (26:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 27) (sixOutputEightSeedSelectedColumns j)%101=
      if (27:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 28) (sixOutputEightSeedSelectedColumns j)%101=
      if (28:Fin 30)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows 29) (sixOutputEightSeedSelectedColumns j)%101=
      if (29:Fin 30)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputEightSeedInverseRows sixOutputEightSeedSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 30,
    natListDot (sixOutputEightSeedInverseRows i) (sixOutputEightSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  intro i
  fin_cases i
  · exact inverse_row0
  · exact inverse_row1
  · exact inverse_row2
  · exact inverse_row3
  · exact inverse_row4
  · exact inverse_row5
  · exact inverse_row6
  · exact inverse_row7
  · exact inverse_row8
  · exact inverse_row9
  · exact inverse_row10
  · exact inverse_row11
  · exact inverse_row12
  · exact inverse_row13
  · exact inverse_row14
  · exact inverse_row15
  · exact inverse_row16
  · exact inverse_row17
  · exact inverse_row18
  · exact inverse_row19
  · exact inverse_row20
  · exact inverse_row21
  · exact inverse_row22
  · exact inverse_row23
  · exact inverse_row24
  · exact inverse_row25
  · exact inverse_row26
  · exact inverse_row27
  · exact inverse_row28
  · exact inverse_row29

theorem sixOutputEightSeedSelected_left_inverse :
    (show Matrix (Fin 30) (Fin 30) (ZMod 101) from
      fun i j => (sixOutputEightSeedInverseRows i).getD j.val 0)*
      sixOutputEightSeedSelected=1 := by
  exact matrix_inverse_of_natListDot 101 30 sixOutputEightSeedInverseRows
    sixOutputEightSeedSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputEightSeedSelected_injective :
    Function.Injective sixOutputEightSeedSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputEightSeedSelected id
    _ sixOutputEightSeedSelected_left_inverse

end FD56
