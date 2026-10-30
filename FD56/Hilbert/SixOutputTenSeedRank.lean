/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputTenSeedData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 45,
    (sixOutputTenSeedInverseRows i).length=45 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 45,
    (sixOutputTenSeedSelectedColumns j).length=45 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 0) (sixOutputTenSeedSelectedColumns j)%101=
      if (0:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 1) (sixOutputTenSeedSelectedColumns j)%101=
      if (1:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 2) (sixOutputTenSeedSelectedColumns j)%101=
      if (2:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 3) (sixOutputTenSeedSelectedColumns j)%101=
      if (3:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 4) (sixOutputTenSeedSelectedColumns j)%101=
      if (4:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 5) (sixOutputTenSeedSelectedColumns j)%101=
      if (5:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 6) (sixOutputTenSeedSelectedColumns j)%101=
      if (6:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 7) (sixOutputTenSeedSelectedColumns j)%101=
      if (7:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 8) (sixOutputTenSeedSelectedColumns j)%101=
      if (8:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 9) (sixOutputTenSeedSelectedColumns j)%101=
      if (9:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 10) (sixOutputTenSeedSelectedColumns j)%101=
      if (10:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 11) (sixOutputTenSeedSelectedColumns j)%101=
      if (11:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 12) (sixOutputTenSeedSelectedColumns j)%101=
      if (12:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 13) (sixOutputTenSeedSelectedColumns j)%101=
      if (13:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 14) (sixOutputTenSeedSelectedColumns j)%101=
      if (14:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 15) (sixOutputTenSeedSelectedColumns j)%101=
      if (15:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 16) (sixOutputTenSeedSelectedColumns j)%101=
      if (16:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 17) (sixOutputTenSeedSelectedColumns j)%101=
      if (17:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 18) (sixOutputTenSeedSelectedColumns j)%101=
      if (18:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 19) (sixOutputTenSeedSelectedColumns j)%101=
      if (19:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 20) (sixOutputTenSeedSelectedColumns j)%101=
      if (20:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 21) (sixOutputTenSeedSelectedColumns j)%101=
      if (21:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 22) (sixOutputTenSeedSelectedColumns j)%101=
      if (22:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 23) (sixOutputTenSeedSelectedColumns j)%101=
      if (23:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 24) (sixOutputTenSeedSelectedColumns j)%101=
      if (24:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 25) (sixOutputTenSeedSelectedColumns j)%101=
      if (25:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 26) (sixOutputTenSeedSelectedColumns j)%101=
      if (26:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 27) (sixOutputTenSeedSelectedColumns j)%101=
      if (27:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 28) (sixOutputTenSeedSelectedColumns j)%101=
      if (28:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 29) (sixOutputTenSeedSelectedColumns j)%101=
      if (29:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 30) (sixOutputTenSeedSelectedColumns j)%101=
      if (30:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 31) (sixOutputTenSeedSelectedColumns j)%101=
      if (31:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 32) (sixOutputTenSeedSelectedColumns j)%101=
      if (32:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 33) (sixOutputTenSeedSelectedColumns j)%101=
      if (33:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 34) (sixOutputTenSeedSelectedColumns j)%101=
      if (34:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 35) (sixOutputTenSeedSelectedColumns j)%101=
      if (35:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 36) (sixOutputTenSeedSelectedColumns j)%101=
      if (36:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 37) (sixOutputTenSeedSelectedColumns j)%101=
      if (37:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 38) (sixOutputTenSeedSelectedColumns j)%101=
      if (38:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 39) (sixOutputTenSeedSelectedColumns j)%101=
      if (39:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row40 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 40) (sixOutputTenSeedSelectedColumns j)%101=
      if (40:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 41) (sixOutputTenSeedSelectedColumns j)%101=
      if (41:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 42) (sixOutputTenSeedSelectedColumns j)%101=
      if (42:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 43) (sixOutputTenSeedSelectedColumns j)%101=
      if (43:Fin 45)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows 44) (sixOutputTenSeedSelectedColumns j)%101=
      if (44:Fin 45)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputTenSeedInverseRows sixOutputTenSeedSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 45,
    natListDot (sixOutputTenSeedInverseRows i) (sixOutputTenSeedSelectedColumns j)%101=
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
  · exact inverse_row40
  · exact inverse_row41
  · exact inverse_row42
  · exact inverse_row43
  · exact inverse_row44

theorem sixOutputTenSeedSelected_left_inverse :
    (show Matrix (Fin 45) (Fin 45) (ZMod 101) from
      fun i j => (sixOutputTenSeedInverseRows i).getD j.val 0)*
      sixOutputTenSeedSelected=1 := by
  exact matrix_inverse_of_natListDot 101 45 sixOutputTenSeedInverseRows
    sixOutputTenSeedSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputTenSeedSelected_injective :
    Function.Injective sixOutputTenSeedSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputTenSeedSelected id
    _ sixOutputTenSeedSelected_left_inverse

end FD56
