/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows0
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows1
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows2
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows3
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows4
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows5
import FD56.Hilbert.BalancedTwentyFiveTangentRankRows6

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 70,
    (balancedTwentyFiveTangentInverseRows i).length=70 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 70,
    (balancedTwentyFiveTangentSelectedColumns j).length=70 := by
  intro j
  fin_cases j <;> rfl

attribute [local irreducible] balancedTwentyFiveTangentInverseRows balancedTwentyFiveTangentSelectedColumns

private theorem inverse_residues (i j : Fin 70) :
    natListDot (balancedTwentyFiveTangentInverseRows i) (balancedTwentyFiveTangentSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFiveTangent_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFiveTangent_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFiveTangent_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFiveTangent_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFiveTangent_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyFiveTangent_inverse_residue_rows_5 i j (by omega) h5
  exact balancedTwentyFiveTangent_inverse_residue_rows_6 i j (by omega) i.isLt

theorem balancedTwentyFiveTangentSelected_left_inverse :
    (show Matrix (Fin 70) (Fin 70) (ZMod 101) from
      fun i j => (balancedTwentyFiveTangentInverseRows i).getD j.val 0)*
      balancedTwentyFiveTangentSelected=1 := by
  exact matrix_inverse_of_natListDot 101 70 balancedTwentyFiveTangentInverseRows
    balancedTwentyFiveTangentSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedTwentyFiveTangentSelected_injective :
    Function.Injective balancedTwentyFiveTangentSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedTwentyFiveTangentSelected id
    _ balancedTwentyFiveTangentSelected_left_inverse

end FD56
