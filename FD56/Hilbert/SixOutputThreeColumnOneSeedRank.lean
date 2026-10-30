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

private theorem inverse_lengths : ∀ i : Fin 20,
    (sixOutputThreeColumnOneSeedInverseRows i).length=20 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 20,
    (sixOutputThreeColumnOneSeedSelectedColumns j).length=20 := by decide +kernel

private theorem inverse_row0 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 0) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (0:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row1 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 1) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (1:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row2 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 2) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (2:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row3 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 3) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (3:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row4 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 4) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (4:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row5 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 5) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (5:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row6 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 6) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (6:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row7 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 7) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (7:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row8 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 8) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (8:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row9 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 9) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (9:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row10 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 10) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (10:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row11 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 11) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (11:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row12 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 12) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (12:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row13 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 13) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (13:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row14 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 14) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (14:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row15 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 15) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (15:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row16 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 16) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (16:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row17 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 17) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (17:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row18 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 18) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (18:Fin 20)=j then 1 else 0 := by decide +kernel

private theorem inverse_row19 : ∀ j : Fin 20,
    natListDot (sixOutputThreeColumnOneSeedInverseRows 19) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
      if (19:Fin 20)=j then 1 else 0 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnOneSeedInverseRows sixOutputThreeColumnOneSeedSelectedColumns

private theorem inverse_residues (i j : Fin 20) :
    natListDot (sixOutputThreeColumnOneSeedInverseRows i) (sixOutputThreeColumnOneSeedSelectedColumns j)%101=
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

theorem sixOutputThreeColumnOneSeedSelected_left_inverse :
    (show Matrix (Fin 20) (Fin 20) (ZMod 101) from
      fun i j => (sixOutputThreeColumnOneSeedInverseRows i).getD j.val 0)*
      sixOutputThreeColumnOneSeedSelected=1 := by
  exact matrix_inverse_of_natListDot 101 20 sixOutputThreeColumnOneSeedInverseRows
    sixOutputThreeColumnOneSeedSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputThreeColumnOneSeedSelected_injective :
    Function.Injective sixOutputThreeColumnOneSeedSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputThreeColumnOneSeedSelected id
    _ sixOutputThreeColumnOneSeedSelected_left_inverse

end FD56
