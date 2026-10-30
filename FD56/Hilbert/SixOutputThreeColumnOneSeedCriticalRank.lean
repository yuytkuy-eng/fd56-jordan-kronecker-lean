/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnOneSeedData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 32,
    (sixOutputThreeColumnOneSeedCriticalInverseRows i).length=32 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 32,
    (sixOutputThreeColumnOneSeedCriticalSelectedColumns j).length=32 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 0) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (0:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 1) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (1:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 2) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (2:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 3) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (3:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 4) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (4:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 5) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (5:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 6) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (6:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 7) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (7:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 8) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (8:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 9) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (9:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 10) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (10:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 11) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (11:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 12) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (12:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 13) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (13:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 14) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (14:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 15) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (15:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 16) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (16:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 17) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (17:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 18) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (18:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 19) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (19:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 20) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (20:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 21) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (21:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 22) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (22:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 23) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (23:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 24) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (24:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 25) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (25:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 26) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (26:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 27) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (27:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 28) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (28:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 29) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (29:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 30) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (30:Fin 32)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 32,
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows 31) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
      if (31:Fin 32)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnOneSeedCriticalInverseRows sixOutputThreeColumnOneSeedCriticalSelectedColumns

private theorem inverse_residues (i j : Fin 32) :
    natListDot (sixOutputThreeColumnOneSeedCriticalInverseRows i) (sixOutputThreeColumnOneSeedCriticalSelectedColumns j)%101=
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
  · exact inverse_row30 j
  · exact inverse_row31 j

theorem sixOutputThreeColumnOneSeedCriticalSelected_left_inverse :
    (show Matrix (Fin 32) (Fin 32) (ZMod 101) from
      fun i j => (sixOutputThreeColumnOneSeedCriticalInverseRows i).getD j.val 0)*
      sixOutputThreeColumnOneSeedCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 32 sixOutputThreeColumnOneSeedCriticalInverseRows
    sixOutputThreeColumnOneSeedCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputThreeColumnOneSeedCriticalSelected_injective :
    Function.Injective sixOutputThreeColumnOneSeedCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputThreeColumnOneSeedCriticalSelected id
    _ sixOutputThreeColumnOneSeedCriticalSelected_left_inverse

end FD56
