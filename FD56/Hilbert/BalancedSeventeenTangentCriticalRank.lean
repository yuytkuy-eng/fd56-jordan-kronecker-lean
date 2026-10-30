/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedSeventeenTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 49,
    (balancedSeventeenTangentCriticalInverseRows i).length=49 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 49,
    (balancedSeventeenTangentCriticalSelectedColumns j).length=49 := by
  intro j
  fin_cases j <;> rfl

private theorem inverse_row0 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 0) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (0:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 1) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (1:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 2) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (2:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 3) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (3:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 4) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (4:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 5) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (5:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 6) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (6:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 7) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (7:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 8) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (8:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 9) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (9:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 10) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (10:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 11) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (11:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 12) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (12:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 13) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (13:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 14) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (14:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 15) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (15:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 16) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (16:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 17) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (17:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 18) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (18:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 19) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (19:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 20) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (20:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 21) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (21:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 22) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (22:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 23) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (23:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 24) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (24:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 25) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (25:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 26) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (26:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 27) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (27:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 28) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (28:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 29) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (29:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 30) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (30:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 31) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (31:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 32) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (32:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 33) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (33:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 34) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (34:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 35) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (35:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 36) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (36:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 37) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (37:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 38) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (38:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 39) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (39:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row40 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 40) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (40:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 41) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (41:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 42) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (42:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 43) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (43:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 44) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (44:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 45) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (45:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 46) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (46:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 47) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (47:Fin 49)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows 48) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
      if (48:Fin 49)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedSeventeenTangentCriticalInverseRows balancedSeventeenTangentCriticalSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 49,
    natListDot (balancedSeventeenTangentCriticalInverseRows i) (balancedSeventeenTangentCriticalSelectedColumns j)%101=
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
  · exact inverse_row45
  · exact inverse_row46
  · exact inverse_row47
  · exact inverse_row48

theorem balancedSeventeenTangentCriticalSelected_left_inverse :
    (show Matrix (Fin 49) (Fin 49) (ZMod 101) from
      fun i j => (balancedSeventeenTangentCriticalInverseRows i).getD j.val 0)*
      balancedSeventeenTangentCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 49 balancedSeventeenTangentCriticalInverseRows
    balancedSeventeenTangentCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedSeventeenTangentCriticalSelected_injective :
    Function.Injective balancedSeventeenTangentCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedSeventeenTangentCriticalSelected id
    _ balancedSeventeenTangentCriticalSelected_left_inverse

end FD56
