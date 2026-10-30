/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 60,
    (balancedTwentyThreeTangentInverseRows i).length=60 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 60,
    (balancedTwentyThreeTangentSelectedColumns j).length=60 := by
  intro j
  fin_cases j <;> rfl

private theorem inverse_row0 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 0) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (0:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 1) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (1:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 2) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (2:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 3) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (3:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 4) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (4:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 5) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (5:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 6) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (6:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 7) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (7:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 8) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (8:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 9) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (9:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 10) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (10:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 11) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (11:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 12) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (12:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 13) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (13:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 14) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (14:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 15) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (15:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 16) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (16:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 17) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (17:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 18) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (18:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 19) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (19:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row20 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 20) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (20:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row21 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 21) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (21:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row22 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 22) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (22:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row23 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 23) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (23:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row24 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 24) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (24:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row25 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 25) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (25:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row26 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 26) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (26:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row27 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 27) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (27:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row28 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 28) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (28:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row29 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 29) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (29:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row30 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 30) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (30:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row31 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 31) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (31:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row32 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 32) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (32:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row33 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 33) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (33:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row34 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 34) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (34:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row35 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 35) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (35:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row36 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 36) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (36:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row37 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 37) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (37:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row38 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 38) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (38:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row39 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 39) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (39:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row40 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 40) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (40:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row41 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 41) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (41:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row42 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 42) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (42:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row43 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 43) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (43:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row44 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 44) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (44:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row45 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 45) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (45:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row46 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 46) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (46:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row47 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 47) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (47:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row48 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 48) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (48:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row49 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 49) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (49:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row50 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 50) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (50:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row51 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 51) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (51:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row52 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 52) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (52:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row53 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 53) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (53:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row54 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 54) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (54:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row55 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 55) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (55:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row56 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 56) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (56:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row57 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 57) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (57:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row58 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 58) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (58:Fin 60)=j then 1 else 0 := by decide +kernel

private theorem inverse_row59 : ∀ j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows 59) (balancedTwentyThreeTangentSelectedColumns j)%101=
      if (59:Fin 60)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] balancedTwentyThreeTangentInverseRows balancedTwentyThreeTangentSelectedColumns

private theorem inverse_residues : ∀ i j : Fin 60,
    natListDot (balancedTwentyThreeTangentInverseRows i) (balancedTwentyThreeTangentSelectedColumns j)%101=
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

theorem balancedTwentyThreeTangentSelected_left_inverse :
    (show Matrix (Fin 60) (Fin 60) (ZMod 101) from
      fun i j => (balancedTwentyThreeTangentInverseRows i).getD j.val 0)*
      balancedTwentyThreeTangentSelected=1 := by
  exact matrix_inverse_of_natListDot 101 60 balancedTwentyThreeTangentInverseRows
    balancedTwentyThreeTangentSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedTwentyThreeTangentSelected_injective :
    Function.Injective balancedTwentyThreeTangentSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedTwentyThreeTangentSelected id
    _ balancedTwentyThreeTangentSelected_left_inverse

end FD56
