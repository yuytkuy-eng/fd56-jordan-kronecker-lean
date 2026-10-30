/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows0
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows1
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows2
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows3
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows4
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows5
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows6
import FD56.Hilbert.BalancedTwentyFiveTangentCriticalBindingRows7

/-! Integral binding of the selected degree7 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 74) :
    balancedTwentyFiveTangentCriticalSelectedCoefficient (K:=K) i j=(balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyFiveTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyFiveTangentCriticalSelectedIntegerEntry]
  rw [balancedTwentyFiveTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyFiveTangentCriticalSelectedIntegerEntry balancedTwentyFiveTangentCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 74) :
    balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyFiveTangentCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_5 i j (by omega) h5
  by_cases h6 : i.val<70
  · exact balancedTwentyFiveTangentCritical_selected_integer_rows_6 i j (by omega) h6
  exact balancedTwentyFiveTangentCritical_selected_integer_rows_7 i j (by omega) i.isLt

theorem balancedTwentyFiveTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyFiveTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedTwentyFiveTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyFiveTangentCritical_selected_binding :
    balancedTwentyFiveTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedTwentyFiveTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyFiveTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyFiveTangentCriticalSelected] using h2

end FD56
