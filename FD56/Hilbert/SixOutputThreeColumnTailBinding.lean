/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows0
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows1
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows2
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows3
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows4
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows5
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows6
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows7
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows8
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows9
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows10
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows11
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows12
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows13
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows14
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows15
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows16
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows17
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows18
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows19
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows20
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows21
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows22
import FD56.Hilbert.SixOutputThreeColumnTailBindingRows23

/-! Integral binding of the kernel-checked degree-five certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
attribute [local irreducible] sixOutputThreeColumnTailCoefficientRows sixOutputThreeColumnTailPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 120) :
    sixOutputThreeColumnTailSelectedCoefficient (K:=K) i j=(sixOutputThreeColumnTailSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputThreeColumnTailSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputThreeColumnTailSelectedIntegerEntry]
  rw [sixOutputThreeColumnTailWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] sixOutputThreeColumnTailSelectedIntegerEntry sixOutputThreeColumnTailSelectedData

private theorem selected_integer_entries (i j : Fin 120) :
    sixOutputThreeColumnTailSelectedIntegerEntry i j%101=(sixOutputThreeColumnTailSelectedData i j : ℤ) := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnTail_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnTail_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnTail_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnTail_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnTail_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnTail_selected_integer_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnTail_selected_integer_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnTail_selected_integer_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnTail_selected_integer_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnTail_selected_integer_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnTail_selected_integer_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnTail_selected_integer_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnTail_selected_integer_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnTail_selected_integer_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnTail_selected_integer_rows_14 i j (by omega) h14
  by_cases h15 : i.val<80
  · exact sixOutputThreeColumnTail_selected_integer_rows_15 i j (by omega) h15
  by_cases h16 : i.val<85
  · exact sixOutputThreeColumnTail_selected_integer_rows_16 i j (by omega) h16
  by_cases h17 : i.val<90
  · exact sixOutputThreeColumnTail_selected_integer_rows_17 i j (by omega) h17
  by_cases h18 : i.val<95
  · exact sixOutputThreeColumnTail_selected_integer_rows_18 i j (by omega) h18
  by_cases h19 : i.val<100
  · exact sixOutputThreeColumnTail_selected_integer_rows_19 i j (by omega) h19
  by_cases h20 : i.val<105
  · exact sixOutputThreeColumnTail_selected_integer_rows_20 i j (by omega) h20
  by_cases h21 : i.val<110
  · exact sixOutputThreeColumnTail_selected_integer_rows_21 i j (by omega) h21
  by_cases h22 : i.val<115
  · exact sixOutputThreeColumnTail_selected_integer_rows_22 i j (by omega) h22
  exact sixOutputThreeColumnTail_selected_integer_rows_23 i j (by omega) i.isLt

theorem sixOutputThreeColumnTail_selected_integer_binding {K : Type*} [Field K] :
    sixOutputThreeColumnTailSelectedCoefficient (K:=K)=
      Matrix.map sixOutputThreeColumnTailSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputThreeColumnTail_selected_binding :
    sixOutputThreeColumnTailSelectedCoefficient (K:=ZMod 101)=sixOutputThreeColumnTailSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputThreeColumnTailSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputThreeColumnTailSelected] using h2

end FD56
