/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.NormalizedSevenTailData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 40,
    (normalizedSevenTailInverseRows i).length=40 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 40,
    (normalizedSevenTailSelectedColumns j).length=40 := by
  intro j
  fin_cases j <;> rfl

private theorem inverse_row0 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 0) (normalizedSevenTailSelectedColumns j)%101=
      if (0:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 1) (normalizedSevenTailSelectedColumns j)%101=
      if (1:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 2) (normalizedSevenTailSelectedColumns j)%101=
      if (2:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 3) (normalizedSevenTailSelectedColumns j)%101=
      if (3:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 4) (normalizedSevenTailSelectedColumns j)%101=
      if (4:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 5) (normalizedSevenTailSelectedColumns j)%101=
      if (5:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 6) (normalizedSevenTailSelectedColumns j)%101=
      if (6:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 7) (normalizedSevenTailSelectedColumns j)%101=
      if (7:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 8) (normalizedSevenTailSelectedColumns j)%101=
      if (8:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 9) (normalizedSevenTailSelectedColumns j)%101=
      if (9:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 10) (normalizedSevenTailSelectedColumns j)%101=
      if (10:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 11) (normalizedSevenTailSelectedColumns j)%101=
      if (11:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 12) (normalizedSevenTailSelectedColumns j)%101=
      if (12:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 13) (normalizedSevenTailSelectedColumns j)%101=
      if (13:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 14) (normalizedSevenTailSelectedColumns j)%101=
      if (14:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 15) (normalizedSevenTailSelectedColumns j)%101=
      if (15:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 16) (normalizedSevenTailSelectedColumns j)%101=
      if (16:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 17) (normalizedSevenTailSelectedColumns j)%101=
      if (17:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 18) (normalizedSevenTailSelectedColumns j)%101=
      if (18:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 19) (normalizedSevenTailSelectedColumns j)%101=
      if (19:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 20) (normalizedSevenTailSelectedColumns j)%101=
      if (20:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 21) (normalizedSevenTailSelectedColumns j)%101=
      if (21:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 22) (normalizedSevenTailSelectedColumns j)%101=
      if (22:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 23) (normalizedSevenTailSelectedColumns j)%101=
      if (23:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 24) (normalizedSevenTailSelectedColumns j)%101=
      if (24:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 25) (normalizedSevenTailSelectedColumns j)%101=
      if (25:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 26) (normalizedSevenTailSelectedColumns j)%101=
      if (26:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 27) (normalizedSevenTailSelectedColumns j)%101=
      if (27:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 28) (normalizedSevenTailSelectedColumns j)%101=
      if (28:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 29) (normalizedSevenTailSelectedColumns j)%101=
      if (29:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 30) (normalizedSevenTailSelectedColumns j)%101=
      if (30:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 31) (normalizedSevenTailSelectedColumns j)%101=
      if (31:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 32) (normalizedSevenTailSelectedColumns j)%101=
      if (32:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 33) (normalizedSevenTailSelectedColumns j)%101=
      if (33:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 34) (normalizedSevenTailSelectedColumns j)%101=
      if (34:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 35) (normalizedSevenTailSelectedColumns j)%101=
      if (35:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 36) (normalizedSevenTailSelectedColumns j)%101=
      if (36:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 37) (normalizedSevenTailSelectedColumns j)%101=
      if (37:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 38) (normalizedSevenTailSelectedColumns j)%101=
      if (38:Fin 40)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 40,
    natListDot (normalizedSevenTailInverseRows 39) (normalizedSevenTailSelectedColumns j)%101=
      if (39:Fin 40)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] normalizedSevenTailInverseRows normalizedSevenTailSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 40,
    natListDot (normalizedSevenTailInverseRows i) (normalizedSevenTailSelectedColumns j)%101=
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

theorem normalizedSevenTailSelected_left_inverse :
    (show Matrix (Fin 40) (Fin 40) (ZMod 101) from
      fun i j => (normalizedSevenTailInverseRows i).getD j.val 0)*
      normalizedSevenTailSelected=1 := by
  exact matrix_inverse_of_natListDot 101 40 normalizedSevenTailInverseRows
    normalizedSevenTailSelectedColumns inverse_lengths column_lengths inverse_residues

theorem normalizedSevenTailSelected_injective :
    Function.Injective normalizedSevenTailSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse normalizedSevenTailSelected id
    _ normalizedSevenTailSelected_left_inverse

end FD56
