/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows0
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows1
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows2
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows3
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows4
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows5
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows6
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows7
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows8
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows9
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows10
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows11
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows12
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows13
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows14
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows15
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows16
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows17
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows18
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalRankRows19
import FD56.LinearAlgebra.NatSelectedInverseCertificate

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 98,
    (sixOutputThreeColumnFourSeedCriticalInverseRows i).length=98 := by decide +kernel

private theorem column_lengths : ∀ j : Fin 98,
    (sixOutputThreeColumnFourSeedCriticalSelectedColumns j).length=98 := by decide +kernel

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalInverseRows sixOutputThreeColumnFourSeedCriticalSelectedColumns

private theorem inverse_residues (i j : Fin 98) :
    natListDot (sixOutputThreeColumnFourSeedCriticalInverseRows i) (sixOutputThreeColumnFourSeedCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_14 i j (by omega) h14
  by_cases h15 : i.val<80
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_15 i j (by omega) h15
  by_cases h16 : i.val<85
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_16 i j (by omega) h16
  by_cases h17 : i.val<90
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_17 i j (by omega) h17
  by_cases h18 : i.val<95
  · exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_18 i j (by omega) h18
  exact sixOutputThreeColumnFourSeedCritical_inverse_residue_rows_19 i j (by omega) i.isLt

theorem sixOutputThreeColumnFourSeedCriticalSelected_left_inverse :
    (show Matrix (Fin 98) (Fin 98) (ZMod 101) from
      fun i j => (sixOutputThreeColumnFourSeedCriticalInverseRows i).getD j.val 0)*
      sixOutputThreeColumnFourSeedCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 98 sixOutputThreeColumnFourSeedCriticalInverseRows
    sixOutputThreeColumnFourSeedCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem sixOutputThreeColumnFourSeedCriticalSelected_injective :
    Function.Injective sixOutputThreeColumnFourSeedCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse sixOutputThreeColumnFourSeedCriticalSelected id
    _ sixOutputThreeColumnFourSeedCriticalSelected_left_inverse

end FD56
