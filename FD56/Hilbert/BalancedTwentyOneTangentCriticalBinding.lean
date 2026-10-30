/-
Copyright 2026 Shifan Yu
SPDX-License-Identifier: Apache-2.0
-/
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingRows0
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingRows1
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingRows2
import FD56.Hilbert.BalancedTwentyOneTangentCriticalBindingRows3

/-! Integral binding of the selected degree6 coefficient minor. -/

noncomputable section
namespace FD56
open Matrix Polynomial
set_option Elab.async false
set_option maxRecDepth 4000
local instance : Fact (Nat.Prime 101) := ⟨by decide⟩

private theorem selected_coefficient_entry {K : Type*} [Field K] (i j : Fin 63) :
    balancedTwentyOneTangentCriticalSelectedCoefficient (K:=K) i j=(balancedTwentyOneTangentCriticalSelectedIntegerEntry i j : K) := by
  dsimp only [balancedTwentyOneTangentCriticalSelectedCoefficient,Matrix.submatrix_apply,
    selectedPolynomialCoefficientMatrix,id_eq,balancedTwentyOneTangentCriticalSelectedIntegerEntry]
  rw [balancedTwentyOneTangentWitness_entry,Polynomial.coeff_mul_X_pow',integerPolynomial_coeff]
  split_ifs <;> simp

private theorem selected_integer_entries (i j : Fin 63) :
    balancedTwentyOneTangentCriticalSelectedIntegerEntry i j%101=(balancedTwentyOneTangentCriticalSelectedData i j : ℤ) := by
  by_cases h0 : i.val<20
  · exact balancedTwentyOneTangentCritical_selected_integer_rows_0 i j (by omega) h0
  by_cases h1 : i.val<40
  · exact balancedTwentyOneTangentCritical_selected_integer_rows_1 i j (by omega) h1
  by_cases h2 : i.val<60
  · exact balancedTwentyOneTangentCritical_selected_integer_rows_2 i j (by omega) h2
  exact balancedTwentyOneTangentCritical_selected_integer_rows_3 i j (by omega) i.isLt

theorem balancedTwentyOneTangentCritical_selected_integer_binding {K : Type*} [Field K] :
    balancedTwentyOneTangentCriticalSelectedCoefficient (K:=K)=Matrix.map balancedTwentyOneTangentCriticalSelectedIntegerEntry (Int.castRingHom K) := by
  funext i j
  exact selected_coefficient_entry i j

theorem balancedTwentyOneTangentCritical_selected_binding :
    balancedTwentyOneTangentCriticalSelectedCoefficient (K:=ZMod 101)=balancedTwentyOneTangentCriticalSelected := by
  funext i j
  rw [selected_coefficient_entry]
  have h := congrArg (fun a : ℤ => (a : ZMod 101)) (selected_integer_entries i j)
  have h2 := (ZMod.intCast_mod (balancedTwentyOneTangentCriticalSelectedIntegerEntry i j) 101).symm.trans h
  simpa only [Int.cast_natCast,balancedTwentyOneTangentCriticalSelected] using h2

end FD56
