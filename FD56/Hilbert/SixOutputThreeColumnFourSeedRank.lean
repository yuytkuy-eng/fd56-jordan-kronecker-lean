/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows0
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows1
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows2
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows3
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows4
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows5
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows6
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows7
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows8
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows9
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows10
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows11
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows12
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows13
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows14
import FD56.Hilbert.SixOutputThreeColumnFourSeedRankRows15
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 80,
    (sixOutputThreeColumnFourSeedInverseRows i).length=80 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 80,
    (sixOutputThreeColumnFourSeedSelectedColumns j).length=80 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedInverseRows sixOutputThreeColumnFourSeedSelectedColumns

private theorem inverse_residues (i j : Fin 80) :
    natListDot (sixOutputThreeColumnFourSeedInverseRows i) (sixOutputThreeColumnFourSeedSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnFourSeed_inverse_residue_rows_14 i j (by omega) h14
  exact sixOutputThreeColumnFourSeed_inverse_residue_rows_15 i j (by omega) i.isLt

theorem sixOutputThreeColumnFourSeedSelected_left_inverse :
    (show Matrix (Fin 80) (Fin 80) (ZMod 101) from
      fun i j => (sixOutputThreeColumnFourSeedInverseRows i).getD j.val 0)*
      sixOutputThreeColumnFourSeedSelected=1 := by
  exact matrix_inverse_of_natListDot 101 80 sixOutputThreeColumnFourSeedInverseRows
    sixOutputThreeColumnFourSeedSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputThreeColumnFourSeedSelected_injective :
    Function.Injective sixOutputThreeColumnFourSeedSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputThreeColumnFourSeedSelected id
    _ sixOutputThreeColumnFourSeedSelected_left_inverse

end FD56
