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

private theorem inverse_lengths : ∀ i : Fin 42,
    (sixOutputEightSeedCriticalInverseRows i).length=42 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 42,
    (sixOutputEightSeedCriticalSelectedColumns j).length=42 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 0) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (0:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 1) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (1:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 2) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (2:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 3) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (3:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 4) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (4:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 5) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (5:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 6) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (6:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 7) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (7:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 8) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (8:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 9) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (9:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 10) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (10:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 11) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (11:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 12) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (12:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 13) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (13:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 14) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (14:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 15) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (15:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 16) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (16:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 17) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (17:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 18) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (18:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 19) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (19:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 20) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (20:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 21) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (21:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 22) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (22:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 23) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (23:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 24) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (24:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 25) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (25:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 26) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (26:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 27) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (27:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 28) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (28:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 29) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (29:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 30) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (30:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 31) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (31:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 32) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (32:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 33) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (33:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 34) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (34:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 35) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (35:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 36) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (36:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 37) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (37:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 38) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (38:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 39) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (39:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row40 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 40) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (40:Fin 42)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows 41) (sixOutputEightSeedCriticalSelectedColumns j)%101=
      if (41:Fin 42)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputEightSeedCriticalInverseRows sixOutputEightSeedCriticalSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 42,
    natListDot (sixOutputEightSeedCriticalInverseRows i) (sixOutputEightSeedCriticalSelectedColumns j)%101=
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

theorem sixOutputEightSeedCriticalSelected_left_inverse :
    (show Matrix (Fin 42) (Fin 42) (ZMod 101) from
      fun i j => (sixOutputEightSeedCriticalInverseRows i).getD j.val 0)*
      sixOutputEightSeedCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 42 sixOutputEightSeedCriticalInverseRows
    sixOutputEightSeedCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputEightSeedCriticalSelected_injective :
    Function.Injective sixOutputEightSeedCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputEightSeedCriticalSelected id
    _ sixOutputEightSeedCriticalSelected_left_inverse

end FD56
