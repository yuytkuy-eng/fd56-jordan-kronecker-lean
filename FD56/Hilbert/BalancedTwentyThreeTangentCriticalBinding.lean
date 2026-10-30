/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows0
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows1
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows2
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows3
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows4
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows5
import FD56.Hilbert.BalancedTwentyThreeTangentCriticalBindingRows6

/-! Integral binding of the selected degree6 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 67) :
    balancedTwentyThreeTangentCriticalSelectedCoefficient (K:=K) i j=(balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyThreeTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyThreeTangentCriticalSelectedIntegerEntry]
  rw [balancedTwentyThreeTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

attribute [local irreducible] balancedTwentyThreeTangentCriticalSelectedIntegerEntry balancedTwentyThreeTangentCriticalSelectedData

private theorem selected_integer_entries (i j : Fin 67) :
    balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyThreeTangentCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<10
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<20
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<30
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_2 i j (by omega) h2
  by_cases h3 : i.val<40
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_3 i j (by omega) h3
  by_cases h4 : i.val<50
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_4 i j (by omega) h4
  by_cases h5 : i.val<60
  · exact balancedTwentyThreeTangentCritical_selected_integer_rows_5 i j (by omega) h5
  exact balancedTwentyThreeTangentCritical_selected_integer_rows_6 i j (by omega) i.isLt

theorem balancedTwentyThreeTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyThreeTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedTwentyThreeTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyThreeTangentCritical_selected_binding :
    balancedTwentyThreeTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedTwentyThreeTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyThreeTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyThreeTangentCriticalSelected] using h2

end FD56
