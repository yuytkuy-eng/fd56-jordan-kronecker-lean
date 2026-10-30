/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 63,
    (balancedTwentyOneTangentCriticalInverseRows i).length=63 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 63,
    (balancedTwentyOneTangentCriticalSelectedColumns j).length=63 := by
  intro j
  fin_cases j <;> rfl

private theorem inverse_row0 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 0) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (0:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 1) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (1:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 2) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (2:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 3) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (3:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 4) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (4:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 5) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (5:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 6) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (6:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 7) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (7:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 8) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (8:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 9) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (9:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 10) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (10:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 11) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (11:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 12) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (12:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 13) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (13:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 14) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (14:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 15) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (15:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 16) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (16:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 17) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (17:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 18) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (18:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 19) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (19:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 20) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (20:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 21) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (21:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 22) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (22:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 23) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (23:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 24) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (24:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 25) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (25:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 26) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (26:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 27) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (27:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 28) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (28:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 29) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (29:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 30) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (30:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 31) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (31:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 32) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (32:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 33) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (33:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 34) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (34:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 35) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (35:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 36) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (36:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 37) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (37:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 38) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (38:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 39) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (39:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row40 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 40) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (40:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 41) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (41:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 42) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (42:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 43) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (43:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 44) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (44:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 45) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (45:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 46) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (46:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 47) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (47:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 48) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (48:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 49) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (49:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row50 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 50) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (50:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 51) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (51:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 52) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (52:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 53) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (53:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 54) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (54:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row55 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 55) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (55:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 56) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (56:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 57) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (57:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 58) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (58:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 59) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (59:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row60 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 60) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (60:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row61 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 61) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (61:Fin 63)=j then 1 else 0 := by decide +kernel

private theorem inverse_row62 : ∀ j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows 62) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
      if (62:Fin 63)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyOneTangentCriticalInverseRows balancedTwentyOneTangentCriticalSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 63,
    natListDot (balancedTwentyOneTangentCriticalInverseRows i) (balancedTwentyOneTangentCriticalSelectedColumns j)%101=
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
  · exact inverse_row49
  · exact inverse_row50
  · exact inverse_row51
  · exact inverse_row52
  · exact inverse_row53
  · exact inverse_row54
  · exact inverse_row55
  · exact inverse_row56
  · exact inverse_row57
  · exact inverse_row58
  · exact inverse_row59
  · exact inverse_row60
  · exact inverse_row61
  · exact inverse_row62

theorem balancedTwentyOneTangentCriticalSelected_left_inverse :
    (show Matrix (Fin 63) (Fin 63) (ZMod 101) from
      fun i j => (balancedTwentyOneTangentCriticalInverseRows i).getD j.val 0)*
      balancedTwentyOneTangentCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 63 balancedTwentyOneTangentCriticalInverseRows
    balancedTwentyOneTangentCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedTwentyOneTangentCriticalSelected_injective :
    Function.Injective balancedTwentyOneTangentCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedTwentyOneTangentCriticalSelected id
    _ balancedTwentyOneTangentCriticalSelected_left_inverse

end FD56
