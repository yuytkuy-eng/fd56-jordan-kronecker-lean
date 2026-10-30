/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows0
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows1
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows2
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows3
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows4
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows5
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows6
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows7
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows8
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows9
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows10
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows11
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows12
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows13
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows14
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows15
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows16
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows17
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows18
import FD56.Hilbert.SixOutputThreeColumnFourSeedCriticalBindingRows19

/-! Integral binding of the kernel-checked degree-4 certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalCoefficientRows sixOutputThreeColumnFourSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 98) :
    sixOutputThreeColumnFourSeedCriticalSelectedCoefficient (K:=K) i j=(sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputThreeColumnFourSeedCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry]
  rw [sixOutputThreeColumnFourSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry sixOutputThreeColumnFourSeedCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 98) :
    sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_14 i j (by omega) h14
  by_cases h15 : i.val<80
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_15 i j (by omega) h15
  by_cases h16 : i.val<85
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_16 i j (by omega) h16
  by_cases h17 : i.val<90
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_17 i j (by omega) h17
  by_cases h18 : i.val<95
  · exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_18 i j (by omega) h18
  exact sixOutputThreeColumnFourSeedCritical_selected_integer_rows_19 i j (by omega) i.isLt

theorem sixOutputThreeColumnFourSeedCritical_selected_integer_binding {K : Type*} [Field K] :
    sixOutputThreeColumnFourSeedCriticalSelectedCoefficient (K:=K)=
      Matrix.map sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputThreeColumnFourSeedCritical_selected_binding :
    sixOutputThreeColumnFourSeedCriticalSelectedCoefficient (K:=ZMod 101)=sixOutputThreeColumnFourSeedCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputThreeColumnFourSeedCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputThreeColumnFourSeedCriticalSelected] using h2

end FD56
