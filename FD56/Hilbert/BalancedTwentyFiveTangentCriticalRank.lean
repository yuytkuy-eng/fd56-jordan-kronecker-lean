/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows0
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows1
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows2
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows3
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows4
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows5
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows6
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalRankRows7

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 74,
    (balancedTwentyFiveTangentCriticalInverseRows i).length=74 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 74,
    (balancedTwentyFiveTangentCriticalSelectedColumns j).length=74 := by
  intro j
  fin_cases j <;> rfl

attribute [local irreducible] balancedTwentyFiveTangentCriticalInverseRows balancedTwentyFiveTangentCriticalSelectedColumns

private theorem inverse_residues (i j : Fin 74) :
    natListDot (balancedTwentyFiveTangentCriticalInverseRows i) (balancedTwentyFiveTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_5 i j (by omega) h5
  by_cases h6 : i.val<70
  · exact balancedTwentyFiveTangentCritical_inverse_residue_rows_6 i j (by omega) h6
  exact balancedTwentyFiveTangentCritical_inverse_residue_rows_7 i j (by omega) i.isLt

theorem balancedTwentyFiveTangentCriticalSelected_left_inverse :
    (show Matrix (Fin 74) (Fin 74) (ZMod 101) from
      fun i j => (balancedTwentyFiveTangentCriticalInverseRows i).getD j.val 0)*
      balancedTwentyFiveTangentCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 74 balancedTwentyFiveTangentCriticalInverseRows
    balancedTwentyFiveTangentCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedTwentyFiveTangentCriticalSelected_injective :
    Function.Injective balancedTwentyFiveTangentCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedTwentyFiveTangentCriticalSelected id
    _ balancedTwentyFiveTangentCriticalSelected_left_inverse

end FD56
