/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailRankRows0
import FD56.Hilbert.SixOutputThreeColumnTailRankRows1
import FD56.Hilbert.SixOutputThreeColumnTailRankRows2
import FD56.Hilbert.SixOutputThreeColumnTailRankRows3
import FD56.Hilbert.SixOutputThreeColumnTailRankRows4
import FD56.Hilbert.SixOutputThreeColumnTailRankRows5
import FD56.Hilbert.SixOutputThreeColumnTailRankRows6
import FD56.Hilbert.SixOutputThreeColumnTailRankRows7
import FD56.Hilbert.SixOutputThreeColumnTailRankRows8
import FD56.Hilbert.SixOutputThreeColumnTailRankRows9
import FD56.Hilbert.SixOutputThreeColumnTailRankRows10
import FD56.Hilbert.SixOutputThreeColumnTailRankRows11
import FD56.Hilbert.SixOutputThreeColumnTailRankRows12
import FD56.Hilbert.SixOutputThreeColumnTailRankRows13
import FD56.Hilbert.SixOutputThreeColumnTailRankRows14
import FD56.Hilbert.SixOutputThreeColumnTailRankRows15
import FD56.Hilbert.SixOutputThreeColumnTailRankRows16
import FD56.Hilbert.SixOutputThreeColumnTailRankRows17
import FD56.Hilbert.SixOutputThreeColumnTailRankRows18
import FD56.Hilbert.SixOutputThreeColumnTailRankRows19
import FD56.Hilbert.SixOutputThreeColumnTailRankRows20
import FD56.Hilbert.SixOutputThreeColumnTailRankRows21
import FD56.Hilbert.SixOutputThreeColumnTailRankRows22
import FD56.Hilbert.SixOutputThreeColumnTailRankRows23
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 120,
    (sixOutputThreeColumnTailInverseRows i).length=120 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 120,
    (sixOutputThreeColumnTailSelectedColumns j).length=120 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnTailInverseRows sixOutputThreeColumnTailSelectedColumns

private theorem inverse_residues (i j : Fin 120) :
    natListDot (sixOutputThreeColumnTailInverseRows i) (sixOutputThreeColumnTailSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnTail_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnTail_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnTail_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnTail_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnTail_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnTail_inverse_residue_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnTail_inverse_residue_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnTail_inverse_residue_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnTail_inverse_residue_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnTail_inverse_residue_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnTail_inverse_residue_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnTail_inverse_residue_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnTail_inverse_residue_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnTail_inverse_residue_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnTail_inverse_residue_rows_14 i j (by omega) h14
  by_cases h15 : i.val<80
  · exact sixOutputThreeColumnTail_inverse_residue_rows_15 i j (by omega) h15
  by_cases h16 : i.val<85
  · exact sixOutputThreeColumnTail_inverse_residue_rows_16 i j (by omega) h16
  by_cases h17 : i.val<90
  · exact sixOutputThreeColumnTail_inverse_residue_rows_17 i j (by omega) h17
  by_cases h18 : i.val<95
  · exact sixOutputThreeColumnTail_inverse_residue_rows_18 i j (by omega) h18
  by_cases h19 : i.val<100
  · exact sixOutputThreeColumnTail_inverse_residue_rows_19 i j (by omega) h19
  by_cases h20 : i.val<105
  · exact sixOutputThreeColumnTail_inverse_residue_rows_20 i j (by omega) h20
  by_cases h21 : i.val<110
  · exact sixOutputThreeColumnTail_inverse_residue_rows_21 i j (by omega) h21
  by_cases h22 : i.val<115
  · exact sixOutputThreeColumnTail_inverse_residue_rows_22 i j (by omega) h22
  exact sixOutputThreeColumnTail_inverse_residue_rows_23 i j (by omega) i.isLt

theorem sixOutputThreeColumnTailSelected_left_inverse :
    (show Matrix (Fin 120) (Fin 120) (ZMod 101) from
      fun i j => (sixOutputThreeColumnTailInverseRows i).getD j.val 0)*
      sixOutputThreeColumnTailSelected=1 := by
  exact matrix_inverse_of_natListDot 101 120 sixOutputThreeColumnTailInverseRows
    sixOutputThreeColumnTailSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputThreeColumnTailSelected_injective :
    Function.Injective sixOutputThreeColumnTailSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputThreeColumnTailSelected id
    _ sixOutputThreeColumnTailSelected_left_inverse

end FD56
