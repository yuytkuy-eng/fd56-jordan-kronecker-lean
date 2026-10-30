/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows0
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows1
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows2
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows3
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows4
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows5
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows6
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows7
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows8
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows9
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows10
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows11
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows12
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows13
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows14
import FD56.Hilbert.SixOutputThreeColumnFourSeedBindingRows15

/-! Integral binding of the kernel-checked degree-3 certificate. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩
attribute [local irreducible] sixOutputThreeColumnFourSeedCoefficientRows sixOutputThreeColumnFourSeedPolynomialData

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 80) :
    sixOutputThreeColumnFourSeedSelectedCoefficient (K:=K) i j=(sixOutputThreeColumnFourSeedSelectedIntegerEntry i j : K) := by
  dsimp only [sixOutputThreeColumnFourSeedSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,sixOutputThreeColumnFourSeedSelectedIntegerEntry]
  rw [sixOutputThreeColumnFourSeedWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] sixOutputThreeColumnFourSeedSelectedIntegerEntry sixOutputThreeColumnFourSeedSelectedData

private theorem selected_integer_entries (i j : Fin 80) :
    sixOutputThreeColumnFourSeedSelectedIntegerEntry i j%101=(sixOutputThreeColumnFourSeedSelectedData i j : ℤ) := by
  by_cases h0 : i.val<5
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<10
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<15
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<20
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<25
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<30
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_5 i j (by omega) h5
  by_cases h6 : i.val<35
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_6 i j (by omega) h6
  by_cases h7 : i.val<40
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_7 i j (by omega) h7
  by_cases h8 : i.val<45
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_8 i j (by omega) h8
  by_cases h9 : i.val<50
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_9 i j (by omega) h9
  by_cases h10 : i.val<55
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_10 i j (by omega) h10
  by_cases h11 : i.val<60
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_11 i j (by omega) h11
  by_cases h12 : i.val<65
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_12 i j (by omega) h12
  by_cases h13 : i.val<70
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_13 i j (by omega) h13
  by_cases h14 : i.val<75
  · exact sixOutputThreeColumnFourSeed_selected_integer_rows_14 i j (by omega) h14
  exact sixOutputThreeColumnFourSeed_selected_integer_rows_15 i j (by omega) i.isLt

theorem sixOutputThreeColumnFourSeed_selected_integer_binding {K : Type*} [Field K] :
    sixOutputThreeColumnFourSeedSelectedCoefficient (K:=K)=
      Matrix.map sixOutputThreeColumnFourSeedSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem sixOutputThreeColumnFourSeed_selected_binding :
    sixOutputThreeColumnFourSeedSelectedCoefficient (K:=ZMod 101)=sixOutputThreeColumnFourSeedSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (sixOutputThreeColumnFourSeedSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,sixOutputThreeColumnFourSeedSelected] using h2

end FD56
