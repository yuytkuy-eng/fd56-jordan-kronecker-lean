/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedEighteenTangentData
import FD56.LinearAlgebra.NatSelectedInverseCertificate
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows0
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows1
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows2
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows3
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows4
import FD56.Hilbert.BalancedEighteenTangentCriticalRankRows5

/-! A kernel-checked selected inverse for the finite tangent coefficient test. -/

namespace FD56
open Matrix
set_option Elab.async false
set_option maxRecDepth 4000
set_option maxHeartbeats 8000000

private theorem inverse_lengths : ∀ i : Fin 54,
    (balancedEighteenTangentCriticalInverseRows i).length=54 := by
  intro i
  fin_cases i <;> rfl

private theorem column_lengths : ∀ j : Fin 54,
    (balancedEighteenTangentCriticalSelectedColumns j).length=54 := by
  intro j
  fin_cases j <;> rfl

attribute [local irreducible] balancedEighteenTangentCriticalInverseRows balancedEighteenTangentCriticalSelectedColumns

private theorem inverse_residues (i j : Fin 54) :
    natListDot (balancedEighteenTangentCriticalInverseRows i) (balancedEighteenTangentCriticalSelectedColumns j)%101=
      if i=j then 1 else 0 := by
  by_cases h0 : i.val<10
  · exact balancedEighteenTangentCritical_inverse_residue_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedEighteenTangentCritical_inverse_residue_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedEighteenTangentCritical_inverse_residue_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedEighteenTangentCritical_inverse_residue_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedEighteenTangentCritical_inverse_residue_rows_4 i j (by omega) h4
  exact balancedEighteenTangentCritical_inverse_residue_rows_5 i j (by omega) i.isLt

theorem balancedEighteenTangentCriticalSelected_left_inverse :
    (show Matrix (Fin 54) (Fin 54) (ZMod 101) from
      fun i j => (balancedEighteenTangentCriticalInverseRows i).getD j.val 0)*
      balancedEighteenTangentCriticalSelected=1 := by
  exact matrix_inverse_of_natListDot 101 54 balancedEighteenTangentCriticalInverseRows
    balancedEighteenTangentCriticalSelectedColumns inverse_lengths column_lengths inverse_residues

theorem balancedEighteenTangentCriticalSelected_injective :
    Function.Injective balancedEighteenTangentCriticalSelected.mulVec := by
  exact mulVec_injective_of_selected_left_inverse balancedEighteenTangentCriticalSelected id
    _ balancedEighteenTangentCriticalSelected_left_inverse

end FD56
