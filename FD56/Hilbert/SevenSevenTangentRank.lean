/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SevenSevenTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 40,
    (sevenSevenTangentInverseRows i).length=40 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 40,
    (sevenSevenTangentSelectedColumns j).length=40 := by
  intro j
  fin_cases j <;> rfl

private theorem inverse_row0 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 0) (sevenSevenTangentSelectedColumns j)%101=
      if (0:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 1) (sevenSevenTangentSelectedColumns j)%101=
      if (1:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 2) (sevenSevenTangentSelectedColumns j)%101=
      if (2:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 3) (sevenSevenTangentSelectedColumns j)%101=
      if (3:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 4) (sevenSevenTangentSelectedColumns j)%101=
      if (4:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 5) (sevenSevenTangentSelectedColumns j)%101=
      if (5:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 6) (sevenSevenTangentSelectedColumns j)%101=
      if (6:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 7) (sevenSevenTangentSelectedColumns j)%101=
      if (7:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 8) (sevenSevenTangentSelectedColumns j)%101=
      if (8:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 9) (sevenSevenTangentSelectedColumns j)%101=
      if (9:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 10) (sevenSevenTangentSelectedColumns j)%101=
      if (10:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 11) (sevenSevenTangentSelectedColumns j)%101=
      if (11:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 12) (sevenSevenTangentSelectedColumns j)%101=
      if (12:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 13) (sevenSevenTangentSelectedColumns j)%101=
      if (13:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 14) (sevenSevenTangentSelectedColumns j)%101=
      if (14:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 15) (sevenSevenTangentSelectedColumns j)%101=
      if (15:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 16) (sevenSevenTangentSelectedColumns j)%101=
      if (16:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 17) (sevenSevenTangentSelectedColumns j)%101=
      if (17:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 18) (sevenSevenTangentSelectedColumns j)%101=
      if (18:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 19) (sevenSevenTangentSelectedColumns j)%101=
      if (19:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 20) (sevenSevenTangentSelectedColumns j)%101=
      if (20:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 21) (sevenSevenTangentSelectedColumns j)%101=
      if (21:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 22) (sevenSevenTangentSelectedColumns j)%101=
      if (22:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 23) (sevenSevenTangentSelectedColumns j)%101=
      if (23:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 24) (sevenSevenTangentSelectedColumns j)%101=
      if (24:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 25) (sevenSevenTangentSelectedColumns j)%101=
      if (25:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 26) (sevenSevenTangentSelectedColumns j)%101=
      if (26:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 27) (sevenSevenTangentSelectedColumns j)%101=
      if (27:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 28) (sevenSevenTangentSelectedColumns j)%101=
      if (28:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 29) (sevenSevenTangentSelectedColumns j)%101=
      if (29:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 30) (sevenSevenTangentSelectedColumns j)%101=
      if (30:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 31) (sevenSevenTangentSelectedColumns j)%101=
      if (31:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 32) (sevenSevenTangentSelectedColumns j)%101=
      if (32:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 33) (sevenSevenTangentSelectedColumns j)%101=
      if (33:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 34) (sevenSevenTangentSelectedColumns j)%101=
      if (34:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 35) (sevenSevenTangentSelectedColumns j)%101=
      if (35:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 36) (sevenSevenTangentSelectedColumns j)%101=
      if (36:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 37) (sevenSevenTangentSelectedColumns j)%101=
      if (37:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 38) (sevenSevenTangentSelectedColumns j)%101=
      if (38:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 40,
    natListDot (sevenSevenTangentInverseRows 39) (sevenSevenTangentSelectedColumns j)%101=
      if (39:Fin 40)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sevenSevenTangentInverseRows sevenSevenTangentSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 40,
    natListDot (sevenSevenTangentInverseRows i) (sevenSevenTangentSelectedColumns j)%101=
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
  · exact inverse_row30
  · exact inverse_row31
  · exact inverse_row32
  · exact inverse_row33
  · exact inverse_row34
  · exact inverse_row35
  · exact inverse_row36
  · exact inverse_row37
  · exact inverse_row38
  · exact inverse_row39

theorem sevenSevenTangentSelected_left_inverse :
    (show Matrix (Fin 40) (Fin 40) (ZMod 101) from
      fun i j => (sevenSevenTangentInverseRows i).getD j.val 0)*
      sevenSevenTangentSelected=1 := by
  exact matrix_inverse_of_natListDot 101 40 sevenSevenTangentInverseRows
    sevenSevenTangentSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sevenSevenTangentSelected_injective :
    Function.Injective sevenSevenTangentSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sevenSevenTangentSelected id
    _ sevenSevenTangentSelected_left_inverse

end FD56
