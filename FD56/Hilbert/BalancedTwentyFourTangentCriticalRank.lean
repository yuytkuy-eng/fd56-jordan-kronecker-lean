/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFourTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows0
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows1
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows2
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows3
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows4
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows5
import FD56.Hilbert.BalancedTwentyFourTangentCriticalRankRows6

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 69,
    (balancedTwentyFourTangentCriticalInverseRows i).length=69 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 69,
    (balancedTwentyFourTangentCriticalSelectedColumns j).length=69 := by
  intro j
  fin_cases j <;> rfl

attribute [local irreducible] balancedTwentyFourTangentCriticalInverseRows balancedTwentyFourTangentCriticalSelectedColumns

private theorem inverse_residues (i j : Fin 69) :
    natListDot (balancedTwentyFourTangentCriticalInverseRows i) (balancedTwentyFourTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyFourTangentCritical_inverse_residue_rows_5 i j (by omega) h5
  exact balancedTwentyFourTangentCritical_inverse_residue_rows_6 i j (by omega) i.isLt

theorem balancedTwentyFourTangentCriticalSelected_left_inverse :
    (show Matrix (Fin 69) (Fin 69) (ZMod 101) from
      fun i j => (balancedTwentyFourTangentCriticalInverseRows i).getD j.val 0)*
      balancedTwentyFourTangentCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 69 balancedTwentyFourTangentCriticalInverseRows
    balancedTwentyFourTangentCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedTwentyFourTangentCriticalSelected_injective :
    Function.Injective balancedTwentyFourTangentCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedTwentyFourTangentCriticalSelected id
    _ balancedTwentyFourTangentCriticalSelected_left_inverse

end FD56
